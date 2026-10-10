import OAI.Analysis.CharacterCriterion.TensorComparison

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
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.InfiniteMaxTensor
open Filter Topology
universe u
variable (D : Type u) [CStarAlgebra D] [instNontrivialD : Nontrivial D]

def pack : ℕ → MaxTensor.CStarPack.{u}
  | 0 => ⟨D,inferInstance⟩
  | n+1 => ⟨MaxTensor.Algebra (pack n) D,inferInstance⟩
abbrev Stage (n : ℕ) := (pack D n).carrier
instance stage_nontrivial (n : ℕ) : Nontrivial (Stage D n) := by
  induction n with
  | zero => exact inferInstanceAs (Nontrivial D)
  | succ n ih => exact inferInstanceAs (Nontrivial (MaxTensor.Algebra (Stage D n) D))
instance stage_separable [TopologicalSpace.SeparableSpace D] (n : ℕ) :
    TopologicalSpace.SeparableSpace (Stage D n) := by
  induction n with
  | zero => exact inferInstanceAs (TopologicalSpace.SeparableSpace D)
  | succ n ih => exact MaxTensor.separable_maxTensor

def chain : CStarInductiveLimit.Chain where
  obj := Stage D
  step _ := MaxTensor.includeLeft
  norm_step n x := (MaxTensor.includeLeft_isometry (A:=Stage D n) (B:=D)).norm_map_of_map_zero (map_zero _) x
abbrev system := (chain D).system
abbrev Algebra := CStarInductiveLimit.Algebra (system D)
instance : CStarAlgebra (Algebra D) := inferInstance
instance : Nontrivial (Algebra D) := by
  let : Nontrivial ((system D).obj 0) := inferInstanceAs (Nontrivial D)
  exact inferInstanceAs (Nontrivial (CStarInductiveLimit.Algebra (system D)))
instance [TopologicalSpace.SeparableSpace D] : TopologicalSpace.SeparableSpace (Algebra D) := by
  let : ∀ n, TopologicalSpace.SeparableSpace ((system D).obj n) := stage_separable D
  exact inferInstanceAs (TopologicalSpace.SeparableSpace (CStarInductiveLimit.Algebra (system D)))

def inclusion (n : ℕ) : Stage D n →⋆ₐ[ℂ] Algebra D := CStarInductiveLimit.of (system D) n
lemma inclusion_isometry (n : ℕ) : Isometry (inclusion D n) := CStarInductiveLimit.of_isometry _ _
lemma inclusion_map (i j : ℕ) (hij : i≤j) (x : Stage D i) :
    inclusion D j ((chain D).map i j hij x)=inclusion D i x := CStarInductiveLimit.of_map _ _ _ _ _
lemma inclusion_step (n : ℕ) (x : Stage D n) :
    inclusion D (n+1) (MaxTensor.includeLeft x)=inclusion D n x := by
  have he := inclusion_map D n (n+1) (Nat.le_succ n) x
  rw [CStarInductiveLimit.Chain.map_succ _ n n le_rfl,CStarInductiveLimit.Chain.map_self] at he
  exact he

def tail (n : ℕ) : D →⋆ₐ[ℂ] Algebra D := (inclusion D (n+1)).comp MaxTensor.includeRight
lemma tail_commutes (i n : ℕ) (hin : i≤n) (x : Stage D i) (d : D) :
    Commute (inclusion D i x) (tail D n d) := by
  rw [←inclusion_map D i n hin x,←inclusion_step D n ((chain D).map i n hin x)]
  exact (MaxTensor.legs_commute ((chain D).map i n hin x) d).map (inclusion D (n+1))

def sequenceHom : D →⋆ₐ[ℂ] NormUltrapower.BoundedSeq (Algebra D) where
  toFun d := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => tail D n d) ‖d‖ (fun n => NonUnitalStarAlgHom.norm_apply_le (tail D n) d)
  map_zero' := by ext n; exact map_zero (tail D n)
  map_one' := by ext n; exact map_one (tail D n)
  map_add' d e := by ext n; exact map_add (tail D n) d e
  map_mul' d e := by ext n; exact map_mul (tail D n) d e
  map_star' d := by ext n; exact map_star (tail D n) d
  commutes' z := by ext n; exact (tail D n).commutes z

lemma sequenceHom_apply (d : D) (n : ℕ) : sequenceHom D d n=tail D n d := rfl
lemma closed_commuting_preimage {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (hφ : Continuous φ) (b : B) :
    IsClosed {a : A | φ a*b=b*φ a} := isClosed_eq (hφ.mul continuous_const) (continuous_const.mul hφ)
lemma central_tail (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) (d : D) :
    NormUltrapower.quotientMap ω (sequenceHom D d)∈NormUltrapower.centralSubalgebra ω := by
  apply (NormUltrapower.mem_central_iff _ _).mpr
  intro x
  apply CStarInductiveLimit.induction_on (system D) x
  · exact closed_commuting_preimage (NormUltrapower.diagonal ω)
      (NormUltrapower.diagonal_isometry ω).continuous _
  · intro i a
    change NormUltrapower.quotientMap ω (NormUltrapower.constantSeq (inclusion D i a)) *
      NormUltrapower.quotientMap ω (sequenceHom D d) = _
    change NormUltrapower.quotientMap ω (NormUltrapower.constantSeq (inclusion D i a)) *
      NormUltrapower.quotientMap ω (sequenceHom D d) =
      NormUltrapower.quotientMap ω (sequenceHom D d)*
      NormUltrapower.quotientMap ω (NormUltrapower.constantSeq (inclusion D i a))
    rw [←map_mul,←map_mul]
    apply Ideal.Quotient.eq.mpr
    apply (NormUltrapower.mem_nullIdeal ω _).mpr
    have he : (fun n => ‖(NormUltrapower.constantSeq (inclusion D i a)*sequenceHom D d-
        sequenceHom D d*NormUltrapower.constantSeq (inclusion D i a)) n‖) =ᶠ[atTop]
        (fun _ => (0:ℝ)) := by
      filter_upwards [eventually_ge_atTop i] with n hn
      change ‖inclusion D i a*tail D n d-tail D n d*inclusion D i a‖=0
      rw [(tail_commutes D i n hn a d).eq,sub_self,norm_zero]
    exact (tendsto_const_nhds.congr' he.symm).mono_left (by simpa only [Nat.cofinite_eq_atTop] using hω)


def toCentral (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    D →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra (Algebra D) ω :=
  StarAlgHom.codRestrict ((NormUltrapower.quotientMap ω).comp (sequenceHom D))
    (NormUltrapower.centralSubalgebra ω) (central_tail D ω hω)

theorem central_no_character (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ))
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (NormUltrapower.CentralAlgebra (Algebra D) ω →⋆ₐ[ℂ] ℂ) :=
  ⟨fun χ => hD.false (χ.comp (toCentral D ω hω))⟩
end KirchbergRordam.InfiniteMaxTensor
namespace KirchbergRordam.TensorHalfFlip
open Filter Topology
open scoped CStarAlgebra
variable {D E C : Type*} [CStarAlgebra D] [CStarAlgebra E] [CStarAlgebra C]
abbrev conj (u : unitary C) := Unitary.conjStarAlgAut ℂ C u

def HalfFlip (D : Type*) [CStarAlgebra D] : Prop :=
  ∃ u : ℕ → unitary (MaxTensor.Algebra D D), ∀ d : D,
    Tendsto (fun n => conj (u n) (MaxTensor.includeLeft d)) atTop
      (𝓝 (MaxTensor.includeRight d))

def mapUnitary (φ : D →⋆ₐ[ℂ] C) (u : unitary D) : unitary C :=
  ⟨φ (u:D),Unitary.map_mem φ u.property⟩
lemma conj_map (φ : D →⋆ₐ[ℂ] C) (u : unitary D) (d : D) :
    conj (mapUnitary φ u) (φ d)=φ (conj u d) := by
  simp only [conj,Unitary.conjStarAlgAut_apply,mapUnitary,map_mul,map_star]
lemma conj_mul (u v : unitary C) (c : C) : conj (u*v) c=conj u (conj v c) := by
  simp only [conj,Unitary.conjStarAlgAut_apply,Submonoid.coe_mul,star_mul,mul_assoc]
lemma conj_fix (u : unitary C) (c : C) (h : Commute (u:C) c) : conj u c=c := by
  change (u:C)*c*star (u:C)=c
  rw [h.eq,mul_assoc,u.property.2,mul_one]

lemma paired_conjugacy
    (lD rD : D →⋆ₐ[ℂ] C) (lE rE : E →⋆ₐ[ℂ] C)
    (hDD : ∀ a b, Commute (lD a) (rD b))
    (hEE : ∀ a b, Commute (lE a) (rE b))
    (hLL : ∀ a b, Commute (lD a) (lE b))
    (hLR : ∀ a b, Commute (lD a) (rE b))
    (hRL : ∀ a b, Commute (rD a) (lE b))
    (hRR : ∀ a b, Commute (rD a) (rE b))
    (hD : HalfFlip D) (hE : HalfFlip E) :
    ∃ u : ℕ → unitary C,
      (∀ d, Tendsto (fun n => conj (u n) (lD d)) atTop (𝓝 (rD d))) ∧
      (∀ e, Tendsto (fun n => conj (u n) (lE e)) atTop (𝓝 (rE e))) := by
  obtain ⟨v,hv⟩ := hD
  obtain ⟨w,hw⟩ := hE
  let α := MaxTensor.lift lD rD hDD
  let β := MaxTensor.lift lE rE hEE
  have αL (d : D) : α (MaxTensor.includeLeft d)=lD d :=
    DFunLike.congr_fun (MaxTensor.lift_includeLeft _ _ _) d
  have αR (d : D) : α (MaxTensor.includeRight d)=rD d :=
    DFunLike.congr_fun (MaxTensor.lift_includeRight _ _ _) d
  have βL (e : E) : β (MaxTensor.includeLeft e)=lE e :=
    DFunLike.congr_fun (MaxTensor.lift_includeLeft _ _ _) e
  have βR (e : E) : β (MaxTensor.includeRight e)=rE e :=
    DFunLike.congr_fun (MaxTensor.lift_includeRight _ _ _) e
  have hDβ (d : D) (y : MaxTensor.Algebra E E) : Commute (lD d) (β y) :=
    maximal_lift_image_commutes lE rE hEE (lD d) (hLL d) (hLR d) y
  have hDβR (d : D) (y : MaxTensor.Algebra E E) : Commute (rD d) (β y) :=
    maximal_lift_image_commutes lE rE hEE (rD d) (hRL d) (hRR d) y
  have hαE (x : MaxTensor.Algebra D D) (e : E) : Commute (α x) (lE e) :=
    (maximal_lift_image_commutes lD rD hDD (lE e)
      (fun d => (hLL d e).symm) (fun d => (hRL d e).symm) x).symm
  have hαβ (x : MaxTensor.Algebra D D) (y : MaxTensor.Algebra E E) : Commute (α x) (β y) :=
    (maximal_lift_image_commutes lD rD hDD (β y)
      (fun d => (hDβ d y).symm) (fun d => (hDβR d y).symm) x).symm
  let U : ℕ → unitary C := fun n => mapUnitary α (v n)*mapUnitary β (w n)
  refine ⟨U,?_,?_⟩
  · intro d
    have he (n : ℕ) : conj (U n) (lD d)=α (conj (v n) (MaxTensor.includeLeft d)) := by
      rw [conj_mul,conj_fix (mapUnitary β (w n)) (lD d) (hDβ d (w n)).symm,←αL,conj_map]
    have ht := ((map_continuous α).tendsto _).comp (hv d)
    rw [αR] at ht
    exact ht.congr (fun n => (he n).symm)
  · intro e
    have hc (n : ℕ) : Commute (α (v n)) (conj (mapUnitary β (w n)) (lE e)) := by
      rw [←βL,conj_map]
      exact hαβ _ _
    have he (n : ℕ) : conj (U n) (lE e)=β (conj (w n) (MaxTensor.includeLeft e)) := by
      rw [conj_mul,conj_fix _ _ (hc n),←βL,conj_map]
    have ht := ((map_continuous β).tendsto _).comp (hw e)
    rw [βR] at ht
    exact ht.congr (fun n => (he n).symm)


theorem tensor (hD : HalfFlip D) (hE : HalfFlip E) :
    HalfFlip (MaxTensor.Algebra D E) := by
  let B := MaxTensor.Algebra D E
  let l : B →⋆ₐ[ℂ] MaxTensor.Algebra B B := MaxTensor.includeLeft
  let r : B →⋆ₐ[ℂ] MaxTensor.Algebra B B := MaxTensor.includeRight
  let d : D →⋆ₐ[ℂ] B := MaxTensor.includeLeft
  let e : E →⋆ₐ[ℂ] B := MaxTensor.includeRight
  obtain ⟨u,huD,huE⟩ := paired_conjugacy (l.comp d) (r.comp d) (l.comp e) (r.comp e)
    (fun a b => MaxTensor.legs_commute (d a) (d b))
    (fun a b => MaxTensor.legs_commute (e a) (e b))
    (fun a b => (MaxTensor.legs_commute a b).map l)
    (fun a b => MaxTensor.legs_commute (d a) (e b))
    (fun a b => (MaxTensor.legs_commute (e b) (d a)).symm)
    (fun a b => (MaxTensor.legs_commute a b).map r) hD hE
  let F : ℕ → B →⋆ₐ[ℂ] MaxTensor.Algebra B B := fun n => (conj (u n)).toStarAlgHom.comp l
  exact ⟨u,MaxTensor.pointwise_limit_of_tensor_legs F r huD huE⟩
end KirchbergRordam.TensorHalfFlip
namespace KirchbergRordam.CStarInductiveLimit
lemma simultaneous_approximation (S : System) (F : Finset (Algebra S)) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ, ∃ a : Algebra S → S.obj n, ∀ x∈F, ‖of S n (a x)-x‖<ε := by
  classical
  choose v hv using fun x : Algebra S => (denseRange_of S).exists_dist_lt x hε
  let n := F.sup (fun x => (v x).1)
  let a : Algebra S → S.obj n := fun x => if hx : x∈F then
    S.map (v x).1 n (Finset.le_sup (f:=fun x => (v x).1) hx) (v x).2 else 0
  refine ⟨n,a,fun x hx => ?_⟩
  dsimp only [a]
  rw [dite_eq_left hx,of_map]
  simpa only [dist_eq_norm,norm_sub_rev] using hv x
end KirchbergRordam.CStarInductiveLimit
namespace KirchbergRordam.TensorHalfFlip
open Filter Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
def squareMap (φ : A →⋆ₐ[ℂ] B) : MaxTensor.Algebra A A →⋆ₐ[ℂ] MaxTensor.Algebra B B :=
  MaxTensor.lift (MaxTensor.includeLeft.comp φ) (MaxTensor.includeRight.comp φ)
    (fun a b => MaxTensor.legs_commute (φ a) (φ b))
lemma squareMap_left (φ : A →⋆ₐ[ℂ] B) (a : A) :
    squareMap φ (MaxTensor.includeLeft a)=MaxTensor.includeLeft (φ a) :=
  DFunLike.congr_fun (MaxTensor.lift_includeLeft _ _ _) a
lemma squareMap_right (φ : A →⋆ₐ[ℂ] B) (a : A) :
    squareMap φ (MaxTensor.includeRight a)=MaxTensor.includeRight (φ a) :=
  DFunLike.congr_fun (MaxTensor.lift_includeRight _ _ _) a
lemma norm_control_map (φ : A →⋆ₐ[ℂ] B) (w : unitary (MaxTensor.Algebra A A)) (a : A) :
    ‖conj (mapUnitary (squareMap φ) w) (MaxTensor.includeLeft (φ a))-MaxTensor.includeRight (φ a)‖≤
      ‖conj w (MaxTensor.includeLeft a)-MaxTensor.includeRight a‖ := by
  rw [←squareMap_left,←squareMap_right,conj_map,←map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le (squareMap φ) _

lemma finite_of_halfFlip (h : HalfFlip A) (F : Finset A) (ε : ℝ) (hε : 0<ε) :
    ∃ u : unitary (MaxTensor.Algebra A A), ∀ a∈F,
      ‖conj u (MaxTensor.includeLeft a)-MaxTensor.includeRight a‖<ε := by
  obtain ⟨u,hu⟩ := h
  have hall : ∀ᶠ n in atTop, ∀ a∈F,
      ‖conj (u n) (MaxTensor.includeLeft a)-MaxTensor.includeRight a‖<ε := by
    apply F.eventually_all.mpr
    intro a ha
    simpa only [dist_eq_norm] using (hu a).eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨n,hn⟩ := hall.exists
  exact ⟨u n,hn⟩


theorem inductive_limit (S : CStarInductiveLimit.System)
    [∀ n, TopologicalSpace.SeparableSpace (S.obj n)]
    (h : ∀ n, HalfFlip (S.obj n)) : HalfFlip (CStarInductiveLimit.Algebra S) := by
  apply FiniteHalfFlipSequence.exists_sequence MaxTensor.includeLeft MaxTensor.includeRight
  intro F ε hε
  classical
  obtain ⟨n,a,ha⟩ := CStarInductiveLimit.simultaneous_approximation S F (ε/4) (by positivity)
  obtain ⟨u,hu⟩ := finite_of_halfFlip (h n) (F.image a) (ε/2) (by positivity)
  let w := mapUnitary (squareMap (CStarInductiveLimit.of S n)) u
  refine ⟨w,fun x hx => ?_⟩
  have hb := (norm_control_map (CStarInductiveLimit.of S n) u (a x)).trans_lt
    (hu (a x) (Finset.mem_image_of_mem a hx))
  have hc := FiniteHalfFlipSequence.perturbation MaxTensor.includeLeft MaxTensor.includeRight w x
    (CStarInductiveLimit.of S n (a x))
  have hd := ha x hx
  rw [norm_sub_rev] at hd
  change ‖conj w (MaxTensor.includeLeft x)-MaxTensor.includeRight x‖≤
    2*‖x-CStarInductiveLimit.of S n (a x)‖+
    ‖conj w (MaxTensor.includeLeft (CStarInductiveLimit.of S n (a x)))-
      MaxTensor.includeRight (CStarInductiveLimit.of S n (a x))‖ at hc
  change ‖conj w (MaxTensor.includeLeft (CStarInductiveLimit.of S n (a x)))-
      MaxTensor.includeRight (CStarInductiveLimit.of S n (a x))‖<ε/2 at hb
  linarith
end KirchbergRordam.TensorHalfFlip
namespace KirchbergRordam.InfiniteMaxTensor
open TensorHalfFlip
universe u
variable (D : Type u) [CStarAlgebra D] [instNontrivialD : Nontrivial D]
omit instNontrivialD in
lemma stage_halfFlip
    (D : Type u)
    [CStarAlgebra D]
    [Nontrivial D]
    (h : HalfFlip D) (n : ℕ) : HalfFlip (Stage D n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact TensorHalfFlip.tensor ih h

theorem halfFlip [TopologicalSpace.SeparableSpace D] (h : HalfFlip D) : HalfFlip (Algebra D) := by
  let : ∀ n, TopologicalSpace.SeparableSpace ((system D).obj n) := stage_separable D
  exact TensorHalfFlip.inductive_limit (system D) (stage_halfFlip D h)
end KirchbergRordam.InfiniteMaxTensor
namespace KirchbergRordam.NormUltrapower
lemma map_central_of_equiv {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (e : X ≃⋆ₐ[ℂ] Y) (ω : Ultrafilter ℕ) (z : CentralAlgebra X ω) :
    map e.toStarAlgHom ω (z : Algebra X ω) ∈ centralSubalgebra ω := by
  apply (mem_central_iff ω _).mpr
  intro b
  let a := e.symm b
  have h := congrArg (map e.toStarAlgHom ω)
    ((mem_central_iff ω (z : Algebra X ω)).mp z.property a)
  simpa only [map_mul,map_diagonal,StarAlgEquiv.toStarAlgHom_apply, a, e.apply_symm_apply] using h
lemma map_equiv_inverse {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (e : X ≃⋆ₐ[ℂ] Y) (ω : Ultrafilter ℕ) (x : Algebra X ω) :
    map e.symm.toStarAlgHom ω (map e.toStarAlgHom ω x)=x := by
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
  change quotientMap ω (sequenceMap e.symm.toStarAlgHom (sequenceMap e.toStarAlgHom y))=quotientMap ω y
  congr 1
  ext n
  exact e.symm_apply_apply (y n)
end KirchbergRordam.NormUltrapower
namespace KirchbergRordam
section
open NormUltrapower


theorem central_isomorphism {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (θ : A ≃⋆ₐ[ℂ] B) (ω : Ultrafilter ℕ) :
    Nonempty (CentralAlgebra A ω ≃⋆ₐ[ℂ] CentralAlgebra B ω) := by
  let f : CentralAlgebra A ω →⋆ₐ[ℂ] CentralAlgebra B ω :=
    StarAlgHom.codRestrict ((NormUltrapower.map θ.toStarAlgHom ω).comp (centralSubalgebra ω).subtype)
      (centralSubalgebra ω) (map_central_of_equiv θ ω)
  let g : CentralAlgebra B ω →⋆ₐ[ℂ] CentralAlgebra A ω :=
    StarAlgHom.codRestrict ((NormUltrapower.map θ.symm.toStarAlgHom ω).comp (centralSubalgebra ω).subtype)
      (centralSubalgebra ω) (map_central_of_equiv θ.symm ω)
  have hgf : Function.LeftInverse g f := by
    intro z
    apply Subtype.ext
    exact map_equiv_inverse θ ω (z : NormUltrapower.Algebra A ω)
  have hfg : Function.RightInverse g f := by
    intro z
    apply Subtype.ext
    exact map_equiv_inverse θ.symm ω (z : NormUltrapower.Algebra B ω)
  exact ⟨StarAlgEquiv.ofBijective f ⟨hgf.injective,hfg.surjective⟩⟩
end
open NormUltrapower
open scoped TensorProduct
universe uTensor


theorem minimal_tensor_central_right (A D : Type uTensor) [CStarAlgebra A] [CStarAlgebra D]
    (ω : Ultrafilter ℕ) :
    Nonempty (CentralAlgebra D ω →⋆ₐ[ℂ] CentralAlgebra (MinTensor.Algebra A D) ω) := by
  let B := MinTensor.Algebra A D
  let l : A →⋆ₐ[ℂ] B := MinTensor.includeLeft
  let r : D →⋆ₐ[ℂ] B := MinTensor.includeRight
  let f : CentralAlgebra D ω →⋆ₐ[ℂ] NormUltrapower.Algebra B ω :=
    (NormUltrapower.map r ω).comp (centralSubalgebra ω).subtype
  have hcentral (z : CentralAlgebra D ω) : f z ∈ centralSubalgebra ω := by
    have hl (a : A) : Commute (diagonal ω (l a)) (f z) := by
      obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (z : NormUltrapower.Algebra D ω)
      change quotientMap ω x=(z : NormUltrapower.Algebra D ω) at hx
      change Commute (diagonal ω (l a)) (NormUltrapower.map r ω (z : NormUltrapower.Algebra D ω))
      rw [← hx,map_mk]
      change quotientMap ω (constantSeq (l a))*quotientMap ω (sequenceMap r x)=
        quotientMap ω (sequenceMap r x)*quotientMap ω (constantSeq (l a))
      rw [← map_mul,← map_mul]
      congr 1
      ext n
      exact (MinTensor.legs_commute a (x n)).eq
    have hr (d : D) : Commute (diagonal ω (r d)) (f z) := by
      have hz := (mem_central_iff ω (z : NormUltrapower.Algebra D ω)).mp z.property d
      have he := congrArg (NormUltrapower.map r ω) hz
      change diagonal ω (r d) * NormUltrapower.map r ω (z : NormUltrapower.Algebra D ω) =
        NormUltrapower.map r ω (z : NormUltrapower.Algebra D ω) * diagonal ω (r d)
      simpa only [map_mul,map_diagonal] using he
    apply (mem_central_iff ω (f z)).mpr
    intro b
    have hclosed : IsClosed {b : B | diagonal ω b*f z=f z*diagonal ω b} :=
      isClosed_eq (((diagonal_isometry (A := B) ω).continuous).mul continuous_const)
        (continuous_const.mul ((diagonal_isometry (A := B) ω).continuous))
    apply (hclosed.closure_subset_iff (s := Set.range (MinTensor.of (A := A) (B := D)))).mpr ?_
      (MinTensor.denseRange_of b)
    rintro b ⟨x,rfl⟩
    obtain ⟨y,rfl⟩ := MinTensor.rawEquiv.surjective x
    change diagonal ω (MinTensor.of (MinTensor.rawEquiv y)) * f z =
      f z * diagonal ω (MinTensor.of (MinTensor.rawEquiv y))
    induction y using TensorProduct.inductionOn with
    | tmul a d =>
      have he : MinTensor.of (MinTensor.rawEquiv (a ⊗ₜ[ℂ] d))=l a*r d := by
        change MinTensor.of (MinTensor.rawEquiv (a ⊗ₜ[ℂ] d))=
          MinTensor.of (MinTensor.rawEquiv (a ⊗ₜ[ℂ] (1:D))) *
            MinTensor.of (MinTensor.rawEquiv ((1:A) ⊗ₜ[ℂ] d))
        rw [← map_mul,← map_mul]
        simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
      rw [he,map_mul]
      exact ((hl a).mul_left (hr d)).eq
    | add x y hx hy =>
      simp only [map_add,add_mul,mul_add]
      rw [hx,hy]
  exact ⟨StarAlgHom.codRestrict f (centralSubalgebra ω) hcentral⟩
end KirchbergRordam
namespace KirchbergRordam.InfiniteMaxTensor
open Filter Topology
open scoped CStarAlgebra
universe u
variable {A D : Type u} [CStarAlgebra A] [CStarAlgebra D] [instNontrivialD : Nontrivial D]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace D]
omit instNontrivialD in
lemma stage_to_central
    {A : Type u}
    {D : Type u}
    [CStarAlgebra A]
    [CStarAlgebra D]
    [Nontrivial D]
    [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace D]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite)
    (φ : D →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) (n : ℕ) :
    Nonempty (Stage D n →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) := by
  induction n with
  | zero => exact ⟨φ⟩
  | succ n ih =>
    obtain ⟨ψ⟩ := ih
    obtain ⟨θ,hθ⟩ := NormUltrapower.relative_commuting_copy ω hω φ ψ
    exact ⟨MaxTensor.lift ψ θ (fun x d => (hθ d x).symm)⟩


theorem exists_central (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite)
    (φ : D →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) :
    Nonempty (Algebra D →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) := by
  let : ∀ n, TopologicalSpace.SeparableSpace ((system D).obj n) := stage_separable D
  exact CStarInductiveLimit.exists_toCentral (system D) ω hω
    (fun n => (stage_to_central ω hω φ n).some)
end KirchbergRordam.InfiniteMaxTensor

namespace KirchbergRordam
open Filter Topology NormUltrapower


theorem infinite_balanced_character_criterion
    (A : Type) [CStarAlgebra A] [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (CentralAlgebra A ω →⋆ₐ[ℂ] ℂ) ↔
      Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A (InfiniteMaxTensor.Algebra BalancedDropLimit.Algebra)) := by
  constructor
  · intro hF
    obtain ⟨φ⟩ := BalancedDropLimit.to_central A ω hω hF
    obtain ⟨ι⟩ := InfiniteMaxTensor.exists_central ω hω φ
    have hhalf : TensorHalfFlip.HalfFlip BalancedDropLimit.Algebra :=
      BalancedDropHalfFlip.exists_half_flip
    obtain ⟨u,hu⟩ := InfiniteMaxTensor.halfFlip BalancedDropLimit.Algebra hhalf
    exact spatial_absorption_of_central_maximal_half_flip A
      (InfiniteMaxTensor.Algebra BalancedDropLimit.Algebra) ω ι u hu
  · rintro ⟨θ⟩
    obtain ⟨e⟩ := central_isomorphism θ ω
    obtain ⟨r⟩ := minimal_tensor_central_right A (InfiniteMaxTensor.Algebra BalancedDropLimit.Algebra) ω
    have hF := InfiniteMaxTensor.central_no_character BalancedDropLimit.Algebra
      BalancedDropLimit.no_character ω hω
    exact ⟨fun χ => hF.false ((χ.comp e.symm.toStarAlgHom).comp r)⟩
end KirchbergRordam
end

end OAI
