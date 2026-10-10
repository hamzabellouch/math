import OAI.Analysis.CharacterCriterion.SymmetryFlow

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.PrimeSquareUnitary
open scoped CStarAlgebra ComplexOrder
open MatrixTensor PrimeDimensionDrop PrimeTensorSections FourLegSymmetries
variable {p q : ℕ}

def diagram (u : unitInterval → unitary (Fiber p q)) (hu : Continuous u) (h0 : u 0=1) :
    SymmetryConjugacyDiagram.Data (SquareFiber p q p q) where
  H := H
  K := K
  hH := H_selfadjoint
  hK := K_selfadjoint
  commute := flips_commute
  L t := Unitary.map (StarMonoidHom.ofClass (MatrixTensor.leftMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q))) (u t)
  continuous_L := by
    apply Continuous.subtype_mk
    exact (continuous_starHom (A:=(Fiber p q)) (B:=(SquareFiber p q p q)) MatrixTensor.leftMatrix).comp (continuous_subtype_val.comp hu)
  L_zero := by
    apply Subtype.ext
    change MatrixTensor.leftMatrix (u 0 : Fiber p q)=1
    rw [h0]
    exact map_one _

variable (u : unitInterval → unitary (Fiber p q)) (hu : Continuous u) (h0 : u 0=1)

lemma R_eq (t : unitInterval) : ((diagram u hu h0).R t : (SquareFiber p q p q))=MatrixTensor.rightMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q) (u t : (Fiber p q)) := by
  exact conj_flip_left (u t : (Fiber p q))
lemma cross_H : (((diagram u hu h0).H*(diagram u hu h0).L 1*(diagram u hu h0).H):(SquareFiber p q p q)) ∈
    tensorRange (MatrixTensor.rightMatrix (ι:=Fin p) (κ:=Fin q)).range (MatrixTensor.leftMatrix (ι:=Fin p) (κ:=Fin q)).range := by
  change (H (P:=Fin p) (Q:=Fin q) : SquareFiber p q p q)*MatrixTensor.leftMatrix (u 1 : Fiber p q)*(H (P:=Fin p) (Q:=Fin q) : SquareFiber p q p q)∈_
  simpa only [Unitary.conjStarAlgAut_apply,H_selfadjoint] using H_cross_mem (u 1 : Fiber p q)
lemma cross_K : (((diagram u hu h0).K*(diagram u hu h0).L 1*(diagram u hu h0).K):(SquareFiber p q p q)) ∈
    tensorRange (MatrixTensor.leftMatrix (ι:=Fin p) (κ:=Fin q)).range (MatrixTensor.rightMatrix (ι:=Fin p) (κ:=Fin q)).range := by
  change (K (P:=Fin p) (Q:=Fin q) : SquareFiber p q p q)*MatrixTensor.leftMatrix (u 1 : Fiber p q)*(K (P:=Fin p) (Q:=Fin q) : SquareFiber p q p q)∈_
  simpa only [Unitary.conjStarAlgAut_apply,K_selfadjoint] using K_cross_mem (u 1 : Fiber p q)

lemma bottom (s : unitInterval) : ((diagram u hu h0).W (s,0):(SquareFiber p q p q))∈tensorRange (⊤ : StarSubalgebra ℂ (Fiber p q)) (MatrixTensor.leftMatrix (ι:=Fin p) (κ:=Fin q)).range := by
  apply (diagram u hu h0).W_bottom_mem
  · exact tensorRange_mono le_top le_rfl H_mem
  · intro t
    exact tensorRange_left _ _ trivial
lemma left (t : unitInterval) : ((diagram u hu h0).W (0,t):(SquareFiber p q p q))∈tensorRange (MatrixTensor.leftMatrix (ι:=Fin p) (κ:=Fin q)).range (⊤ : StarSubalgebra ℂ (Fiber p q)) := by
  apply (diagram u hu h0).W_left_mem
  · exact tensorRange_mono le_rfl le_top H_mem
  · intro t; rw [R_eq]; exact tensorRange_right _ _ trivial
  · exact tensorRange_mono le_rfl le_top (cross_K u hu h0)
lemma right (t : unitInterval) : ((diagram u hu h0).W (1,t):(SquareFiber p q p q))∈tensorRange (MatrixTensor.rightMatrix (ι:=Fin p) (κ:=Fin q)).range (⊤ : StarSubalgebra ℂ (Fiber p q)) := by
  apply (diagram u hu h0).W_right_mem
  · exact tensorRange_mono le_rfl le_top K_mem
  · intro t; rw [R_eq]; exact tensorRange_right _ _ trivial
  · exact tensorRange_mono le_rfl le_top (cross_H u hu h0)
lemma top (s : unitInterval) : ((diagram u hu h0).W (s,1):(SquareFiber p q p q))∈tensorRange (⊤ : StarSubalgebra ℂ (Fiber p q)) (MatrixTensor.rightMatrix (ι:=Fin p) (κ:=Fin q)).range := by
  apply (diagram u hu h0).W_top_mem
  · exact tensorRange_mono le_top le_rfl K_mem
  · intro t; exact tensorRange_left _ _ trivial
  · exact tensorRange_mono le_top le_rfl (cross_K u hu h0)

lemma corner00 : (diagram u hu h0).W (0,0)=(diagram u hu h0).H := by
  rw [(diagram u hu h0).W_bottom]
  simp [SymmetryConjugacyDiagram.Data.Hp,(diagram u hu h0).L_zero,mul_assoc]
lemma corner10 : (diagram u hu h0).W (1,0)=star ((diagram u hu h0).H*(diagram u hu h0).L 1*(diagram u hu h0).H) := by
  rw [(diagram u hu h0).W_right]
  simp only [(diagram u hu h0).R_zero,SymmetryConjugacyDiagram.Data.Kp,UnitaryConjugacySquare.symmetry,
    show ((0:unitInterval):ℝ)=0 from rfl,
    SymmetryFlow.flow_zero,one_mul,star_mul,(diagram u hu h0).H_star,mul_assoc]
lemma corner01 : (diagram u hu h0).W (0,1)=(diagram u hu h0).K*(diagram u hu h0).L 1*(diagram u hu h0).K := by
  rw [(diagram u hu h0).W_top]
  simp [SymmetryConjugacyDiagram.Data.Kp,(diagram u hu h0).L_zero]
lemma corner11 : (diagram u hu h0).W (1,1)=(diagram u hu h0).K := by
  rw [(diagram u hu h0).W_top]
  simp only [show ((1:unitInterval):ℝ)=1 from rfl,(diagram u hu h0).Kp_one]
  rw [mul_assoc ((diagram u hu h0).K*(diagram u hu h0).L 1), (diagram u hu h0).KK,mul_one]
  simp [mul_assoc]

lemma fibers (x : Square) : ((diagram u hu h0).W x:(SquareFiber p q p q))∈fiberRange (p:=p) (q:=q) (r:=p) (k:=q) x := by
  rcases x with ⟨s,t⟩
  change _∈tensorRange (evaluation p q s).range (evaluation p q t).range
  by_cases hs0 : s=0
  · subst s
    rw [evaluation_zero_range]
    by_cases ht0 : t=0
    · subst t; rw [evaluation_zero_range,corner00]; exact H_mem
    by_cases ht1 : t=1
    · subst t; rw [evaluation_one_range,corner01]; exact cross_K u hu h0
    rw [evaluation_interior_range t ht0 ht1]; exact left u hu h0 t
  by_cases hs1 : s=1
  · subst s
    rw [evaluation_one_range]
    by_cases ht0 : t=0
    · subst t; rw [evaluation_zero_range,corner10]
      exact (tensorRange _ _).star_mem' (cross_H u hu h0)
    by_cases ht1 : t=1
    · subst t; rw [evaluation_one_range,corner11]; exact K_mem
    rw [evaluation_interior_range t ht0 ht1]; exact right u hu h0 t
  rw [evaluation_interior_range s hs0 hs1]
  by_cases ht0 : t=0
  · subst t; rw [evaluation_zero_range]; exact bottom u hu h0 s
  by_cases ht1 : t=1
  · subst t; rw [evaluation_one_range]; exact top u hu h0 s
  rw [evaluation_interior_range t ht0 ht1,tensorRange_top_top]
  trivial

def unitarySection : C(Square,(SquareFiber p q p q)) := ⟨fun x => ((diagram u hu h0).W x:(SquareFiber p q p q)),continuous_subtype_val.comp (diagram u hu h0).W_continuous⟩
lemma section_mem : unitarySection u hu h0∈sectionRange (p:=p) (q:=q) (r:=p) (k:=q) :=
  mem_sectionRange_of_fibers _ (fibers u hu h0)

def continuousUnitary {X B : Type*} [TopologicalSpace X] [CompactSpace X]
    [CStarAlgebra B] (f : X → unitary B) (hf : Continuous f) : unitary C(X,B) :=
  ⟨⟨fun x => (f x : B),continuous_subtype_val.comp hf⟩,by
    constructor
    · apply ContinuousMap.ext; intro x; exact (f x).property.1
    · apply ContinuousMap.ext; intro x; exact (f x).property.2⟩

lemma unitary_lift {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) (v : unitary B)
    (hv : (v:B)∈φ.range) : ∃ w : unitary A, φ (w:A)=(v:B) := by
  obtain ⟨a,ha⟩ := hv
  have ha' : φ a=(v:B) := ha
  have hu : a∈unitary A := by
    constructor <;> apply hφ
    · simpa only [map_mul,map_star,map_one,ha'] using v.property.1
    · simpa only [map_mul,map_star,map_one,ha'] using v.property.2
  exact ⟨⟨a,hu⟩,ha⟩

lemma section_unitary : unitarySection u hu h0∈unitary C(Square,SquareFiber p q p q) := by
  constructor
  · apply ContinuousMap.ext; intro x
    exact ((diagram u hu h0).W x).property.1
  · apply ContinuousMap.ext; intro x
    exact ((diagram u hu h0).W x).property.2

lemma section_exists_raw : ∃ w : MaxTensor.Algebra (Algebra p q) (Algebra p q),
    sectionMap w=unitarySection u hu h0 := section_mem (p:=p) (q:=q) u hu h0

lemma reflect_unitary {A B : Type*} [Semiring A] [StarMul A] [_root_.Algebra ℂ A]
    [Semiring B] [StarMul B] [_root_.Algebra ℂ B]
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) (a : A) (ha : φ a∈unitary B) :
    a∈unitary A := by
  constructor <;> apply hφ
  · simpa only [map_mul,map_star,map_one] using ha.1
  · simpa only [map_mul,map_star,map_one] using ha.2

lemma section_image_unitary (w : MaxTensor.Algebra (Algebra p q) (Algebra p q))
    (hw : sectionMap w=unitarySection u hu h0) :
    sectionMap (p:=p) (q:=q) (r:=p) (k:=q) w∈unitary C(Square,SquareFiber p q p q) := by
  rw [hw]
  exact section_unitary u hu h0

lemma section_reflect (w : MaxTensor.Algebra (Algebra p q) (Algebra p q))
    (hw : sectionMap w=unitarySection u hu h0) :
    w∈unitary (MaxTensor.Algebra (Algebra p q) (Algebra p q)) := by
  have h := section_image_unitary u hu h0 w hw
  constructor
  · apply sectionMap_injective (p:=p) (q:=q) (r:=p) (k:=q)
    calc
      sectionMap (star w*w) = star (sectionMap w)*sectionMap w := by rw [map_mul,map_star]
      _ = 1 := h.1
      _ = sectionMap 1 := (sectionMap (p:=p) (q:=q) (r:=p) (k:=q)).map_one'.symm
  · apply sectionMap_injective (p:=p) (q:=q) (r:=p) (k:=q)
    calc
      sectionMap (w*star w) = sectionMap w*star (sectionMap w) := by rw [map_mul,map_star]
      _ = 1 := h.2
      _ = sectionMap 1 := (sectionMap (p:=p) (q:=q) (r:=p) (k:=q)).map_one'.symm


theorem exists_unitary : ∃ w : unitary (MaxTensor.Algebra (Algebra p q) (Algebra p q)),
    sectionMap (w : MaxTensor.Algebra (Algebra p q) (Algebra p q))=unitarySection u hu h0 := by
  obtain ⟨w,hw⟩ := section_exists_raw (p:=p) (q:=q) u hu h0
  exact ⟨⟨w,section_reflect u hu h0 w hw⟩,hw⟩
end KirchbergRordam.PrimeSquareUnitary
namespace KirchbergRordam.PrimeSquareUnitary
open scoped CStarAlgebra ComplexOrder
open MatrixTensor PrimeDimensionDrop PrimeTensorSections FourLegSymmetries
open UnitaryDisplacement
variable {p q : ℕ}

lemma conj_map {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (u : unitary A) (a : A) :
    conj (Unitary.map (StarMonoidHom.ofClass φ) u) (φ a)=φ (conj u a) := by
  change φ (u:A)*φ a*star (φ (u:A))=φ ((u:A)*a*star (u:A))
  rw [map_mul,map_mul,map_star]
lemma conj_commute (u : unitary (SquareFiber p q p q)) (a : (SquareFiber p q p q)) (h : conj u a=a) : Commute (u:(SquareFiber p q p q)) a := by
  have hh := congrArg (fun x : (SquareFiber p q p q) => x*(u:(SquareFiber p q p q))) h
  change (u:SquareFiber p q p q)*a=a*(u:SquareFiber p q p q)
  simpa only [conj,Unitary.conjStarAlgAut_apply,mul_assoc,Unitary.coe_star_mul_self,mul_one] using hh

lemma pointwise_control (u : unitInterval → unitary (Fiber p q)) (hu : Continuous u) (h0 : u 0=1)
    (f : PrimeDimensionDrop.Algebra p q) (δ : ℝ)
    (hf : ∀ t, ‖conj (star (u t)) (f.val t)-f.val 0‖≤δ) (s t : unitInterval) :
    ‖conj ((diagram u hu h0).W (s,t)) (MatrixTensor.leftMatrix (f.val s))-
      MatrixTensor.rightMatrix (f.val t)‖≤4*δ := by
  let a : unitInterval → (SquareFiber p q p q) := fun t => MatrixTensor.leftMatrix (conj (star (u t)) (f.val t))
  let b : (SquareFiber p q p q) := MatrixTensor.leftMatrix (f.val 1)
  have ha0 : a 0=MatrixTensor.leftMatrix (f.val 0) := by simp [a,h0,conj]
  have ha : Commute ((diagram u hu h0).K:(SquareFiber p q p q)) (a 0) := by
    rw [ha0]
    obtain ⟨v,hv⟩ := f.property.1
    change MatrixTensor.leftMatrix v=f.val 0 at hv
    rw [←hv]
    exact conj_commute _ _ (conj_K_left_left v)
  have hb : Commute ((diagram u hu h0).H:(SquareFiber p q p q)) b := by
    obtain ⟨v,hv⟩ := f.property.2
    change Commute _ (MatrixTensor.leftMatrix (f.val 1))
    change MatrixTensor.rightMatrix v=f.val 1 at hv
    rw [←hv]
    exact conj_commute _ _ (conj_H_left_right v)
  have haN (r : unitInterval) : ‖a r-a 0‖≤δ := by
    rw [ha0]
    change ‖MatrixTensor.leftMatrix _-MatrixTensor.leftMatrix _‖≤δ
    rw [←map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le (MatrixTensor.leftMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q)) _).trans (hf r)
  have hcancel (r : unitInterval) : conj ((diagram u hu h0).L r) (a r)=MatrixTensor.leftMatrix (f.val r) := by
    rw [show (diagram u hu h0).L r=Unitary.map (StarMonoidHom.ofClass (MatrixTensor.leftMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q))) (u r) from rfl]
    change conj (Unitary.map (StarMonoidHom.ofClass (MatrixTensor.leftMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q))) (u r))
      (MatrixTensor.leftMatrix (conj (star (u r)) (f.val r)))=_
    rw [conj_map]
    congr 1
    simpa only [star_star] using conj_star (star (u r)) (f.val r)
  have hend : ‖conj ((diagram u hu h0).L 1) (a 0)-b‖≤δ := by
    change ‖conj ((diagram u hu h0).L 1) (a 0)-MatrixTensor.leftMatrix (f.val 1)‖≤δ
    rw [←hcancel 1,norm_sub,norm_sub_rev]
    exact haN 1
  have hh := (diagram u hu h0).half_flip_control a b ha hb δ haN hend s t
  rw [hcancel] at hh
  have hr : conj ((diagram u hu h0).R t)
      (conj ((diagram u hu h0).H*(diagram u hu h0).K) (a t))=MatrixTensor.rightMatrix (f.val t) := by
    change conj ((diagram u hu h0).R t) (conj (H*K) (MatrixTensor.leftMatrix (conj (star (u t)) (f.val t))))=_
    rw [conj_flip_left]
    have hm : (diagram u hu h0).R t=Unitary.map
        (StarMonoidHom.ofClass (MatrixTensor.rightMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q))) (u t) :=
      Subtype.ext (R_eq u hu h0 t)
    rw [hm,conj_map]
    congr 1
    simpa only [star_star] using conj_star (star (u t)) (f.val t)
  rwa [hr] at hh

lemma norm_bound_in_sections {A B X : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace X] [CompactSpace X] (φ : A →⋆ₐ[ℂ] C(X,B)) (hφ : Isometry φ)
    (w : unitary A) (a b : A) (c : ℝ) (hc : 0≤c)
    (h : ∀ x, ‖(φ (w:A)) x*(φ a) x*star ((φ (w:A)) x)-(φ b) x‖≤c) :
    ‖conj w a-b‖≤c := by
  rw [←hφ.norm_map_of_map_zero (map_zero φ)]
  apply (ContinuousMap.norm_le _ hc).mpr
  intro x
  simpa only [conj,Unitary.conjStarAlgAut_apply,map_sub,map_mul,map_star,
    ContinuousMap.sub_apply,ContinuousMap.mul_apply,ContinuousMap.star_apply] using h x


theorem exists_half_flip_control (u : unitInterval → unitary (Fiber p q))
    (hu : Continuous u) (h0 : u 0=1) :
    ∃ w : unitary (MaxTensor.Algebra (PrimeDimensionDrop.Algebra p q) (PrimeDimensionDrop.Algebra p q)),
      ∀ (f : PrimeDimensionDrop.Algebra p q) (δ : ℝ),
        (∀ t, ‖conj (star (u t)) (f.val t)-f.val 0‖≤δ) →
        ‖conj w (MaxTensor.includeLeft f)-MaxTensor.includeRight f‖≤4*δ := by
  obtain ⟨w,hw⟩ := exists_unitary u hu h0
  refine ⟨w,fun f δ hf => ?_⟩
  have hδ : 0≤δ := (norm_nonneg _).trans (hf 0)
  apply norm_bound_in_sections sectionMap sectionMap_isometry w
    (MaxTensor.includeLeft f) (MaxTensor.includeRight f) (4*δ) (by positivity)
  intro x
  rcases x with ⟨s,t⟩
  rw [hw,sectionMap_left,sectionMap_right]
  exact pointwise_control u hu h0 f δ hf s t
end KirchbergRordam.PrimeSquareUnitary


end

end OAI
