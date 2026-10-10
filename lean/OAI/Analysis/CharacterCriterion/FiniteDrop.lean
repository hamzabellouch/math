import OAI.Analysis.CharacterCriterion.FullComparison

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
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.ConeDrop
open scoped CStarAlgebra ComplexOrder BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor ConeModel
local instance : PartialOrder Cone := CStarAlgebra.spectralOrder _
local instance : LE Cone := (CStarAlgebra.spectralOrder Cone).toLE
local instance : StarOrderedRing Cone := CStarAlgebra.spectralOrderedRing _
variable {P : Type*} [CStarAlgebra P]
local instance (n : ℕ) : PartialOrder (powerPack P n) := CStarAlgebra.spectralOrder _
local instance (n : ℕ) : StarOrderedRing (powerPack P n) := CStarAlgebra.spectralOrderedRing _

lemma map_y (η : Cone →⋆ₐ[ℂ] P) (k : ℕ) (δ : ℝ) (hδ : 0≤δ) (j : Fin (k+1)) :
    powerHom η k (ConeCube.y k δ hδ j)=cornerWord k (η (ConeCut.q δ hδ)) (η (ConeCut.g δ)) j := by
  rw [ConeCube.y,powerHom_word,cornerWord]
  congr 1
  funext i
  split_ifs <;> rfl
lemma map_defect (η : Cone →⋆ₐ[ℂ] P) (k : ℕ) (δ : ℝ) :
    1-powerHom η k (ConeCube.h k δ)=defectWord k (η (ConeCut.g δ)) := by
  rw [← map_one (powerHom η k),← map_sub,ConeCube.defect_word,powerHom_word]
  rfl
lemma map_fix (η : Cone →⋆ₐ[ℂ] P) (k : ℕ) {δ : ℝ} (hδ : 0<δ) (j : Fin (k+1)) :
    powerHom η k (ConeCube.x k δ 0 0)*cornerWord k (η (ConeCut.q δ hδ.le)) (η (ConeCut.g δ)) j=
      cornerWord k (η (ConeCut.q δ hδ.le)) (η (ConeCut.g δ)) j := by
  rw [← map_y,← map_mul,ConeCube.x_fixes_y k hδ j]

omit instSize instPauliData in
lemma map_nonneg_generic
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    [pE : PartialOrder E] [StarOrderedRing E] [PartialOrder F] [StarOrderedRing F]
    (φ : E →⋆ₐ[ℂ] F) {a : E} (ha : 0≤a) : 0≤φ a := map_nonneg φ ha
variable [Nontrivial P] [PartialOrder P] [StarOrderedRing P]


theorem exists_drop_from_full_cone (η : Cone →⋆ₐ[ℂ] P)
    (hfull : Fullness.IsFull (η (ConeCut.q 0 (le_refl 0)))) :
    ∃ m : ℕ, Nonempty (DimensionDrop23 →⋆ₐ[ℂ] powerPack P m) := by
  classical
  obtain ⟨δ,hδ,hδ1,hfullδ⟩ := ConeCut.exists_full_cut η hfull
  let c := η (ConeCut.q δ hδ.le)
  let G := η (ConeCut.g δ)
  let z : Fin 2→P := fun i=>η (ConeCut.z δ hδ.le (Fin.castLE PauliData.two_le i))
  have hz (i j : Fin 2) : star (z i)*z j=if i=j then c else 0 := by
    dsimp only [z,c]
    rw [← map_star,← map_mul,ConeCut.z_gram]
    have he : (Fin.castLE PauliData.two_le i = Fin.castLE PauliData.two_le j) ↔ i=j :=
      (Fin.castLE_injective PauliData.two_le).eq_iff
    simp only [he, apply_ite, map_zero]
    split_ifs <;> rfl
  have hc : 0≤c := by rw [← show star (z 0)*z 0=c by simpa using hz 0 0]; exact star_mul_self_nonneg _
  have hG : 0≤G := map_nonneg_generic (pE:=CStarAlgebra.spectralOrder Cone) η (ConeCut.g_nonneg δ)
  have hcG : c*G=0 := by dsimp only [c,G]; rw [← map_mul,ConeCut.qg_zero hδ,map_zero]
  obtain ⟨N,v,hv⟩ := FullComparison.full_comparison hc hfullδ
  have hN : N≠0 := by intro he; subst N; simp at hv
  let : NeZero N := ⟨hN⟩
  obtain ⟨L,e,a,b,ha,hb⟩ := auxiliary c v hv z hz
  let J := Fin (L+1)→Fin N
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α:=J))
  let σ : Fin (k+1)≃J := (Fintype.equivFinOfCardEq hk).symm
  let Y : Fin (k+1)→powerPack P k := cornerWord k c G
  let U : Fin (k+1)→Fin N→powerPack P k := fun j i=>columnWord k G j (v i)
  let V : Fin (k+1)→powerPack P L := fun j=>b (σ j)
  have hV : ∑ j,star (V j)*e*V j=1 := by
    have he := σ.sum_comp (fun j=>star (b j)*e*b j)
    exact he.trans hb
  let B := MaxTensor.Algebra (powerPack P k) (powerPack P L)
  let : PartialOrder B := CStarAlgebra.spectralOrder _
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
  let φ : powerPack P k →⋆ₐ[ℂ] B := includeLeft
  let ψ : powerPack P L →⋆ₐ[ℂ] B := includeRight
  let W := ((ConeCube.weighted k hδ).map (powerHom η k)).map φ
  have hY (j) : 0≤Y j := cornerWord_nonneg k hc hG j
  have hYY (j l) (hjl : j≠l) : Y j*Y l=0 := cornerWord_orthogonal k hcG j l hjl
  have hU (j) : ∑ i,star (U j i)*Y j*U j i=defectWord k G := columnWord_comparison k hG v hv j
  have hcomp := AmplifiedComparison.compare φ ψ (fun x y=>legs_commute x y)
    Y hY hYY U a V e ha (defectWord k G) hU hV
  have hsum : 0≤φ (∑ j,Y j) := map_nonneg φ (Finset.sum_nonneg (fun j _=>hY j))
  have hfix : W.x 0 0*φ (∑ j,Y j)=φ (∑ j,Y j) := by
    change φ (powerHom η k (ConeCube.x k δ 0 0))*φ (∑ j,Y j)=_
    rw [← map_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact map_fix η k hδ j
  have hcut := support_cut_comparison (W.star_x 0 0) hsum hfix
  have hdef : 1-W.h=φ (defectWord k G) := by
    change 1-φ (powerHom η k (ConeCube.h k δ))=_
    rw [← map_one φ,← map_sub,map_defect]
  have hw : CuntzBelow (1-W.h) (ExactCut.cut (W.x 0 0) (1/2)) := by
    rw [hdef]
    exact hcomp.trans hcut
  obtain ⟨flatten⟩ := exists_joinPower P k L
  exact ⟨k+L+1,⟨flatten.comp (W.cutoffHom hw)⟩⟩
end KirchbergRordam.GenericRW.ConeDrop

namespace KirchbergRordam.GenericRW.MaxTensor
open scoped BigOperators
universe u
variable {P Q : Type u} [CStarAlgebra P] [CStarAlgebra Q]

omit instSize instPauliData in
lemma norm_pure_le
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    (a : P) (b : Q) : ‖pure a b‖≤‖a‖*‖b‖ :=
  (norm_mul_le _ _).trans (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le includeLeft a)
    (NonUnitalStarAlgHom.norm_apply_le includeRight b) (norm_nonneg _) (norm_nonneg _))

variable [PartialOrder P] [StarOrderedRing P] [PartialOrder Q] [StarOrderedRing Q]
local instance : PartialOrder (Algebra P Q) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (Algebra P Q) := CStarAlgebra.spectralOrderedRing _
lemma pure_nonneg {a : P} {b : Q} (ha : 0≤a) (hb : 0≤b) : 0≤pure a b := by
  have he : star (pure (CFC.sqrt a) (CFC.sqrt b))*pure (CFC.sqrt a) (CFC.sqrt b)=pure a b := by
    rw [pure_star,pure_mul,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq,
      CFC.sqrt_mul_sqrt_self _ ha,CFC.sqrt_mul_sqrt_self _ hb]
  rw [← he]
  exact star_mul_self_nonneg _
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor OrderZero Fullness
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
local instance : PartialOrder (Algebra A B) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (Algebra A B) := CStarAlgebra.spectralOrderedRing _

def tensor (W : WeightedUnits I A) (V : WeightedUnits J B) : WeightedUnits (I×J) (Algebra A B) where
  h := pure W.h V.h
  x i j := pure (W.x i.1 j.1) (V.x i.2 j.2)
  nonneg := pure_nonneg W.nonneg V.nonneg
  norm_le := (norm_pure_le _ _).trans (by nlinarith [W.norm_le,V.norm_le,norm_nonneg W.h,norm_nonneg V.h])
  star_x i j := by rw [pure_star,W.star_x,V.star_x]
  mul_x i j k l := by
    rw [pure_mul,W.mul_x,V.mul_x]
    by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2 <;>
      simp [h1,h2,Prod.ext_iff,pure_mul]
  diagonal := by
    simp only [Fintype.sum_prod_type,← pure_sum_right,← pure_sum_left,W.diagonal,V.diagonal]

def reindex (W : WeightedUnits I A) (e : I ≃ J) : WeightedUnits J A where
  h := W.h
  x i j := W.x (e.symm i) (e.symm j)
  nonneg := W.nonneg
  norm_le := W.norm_le
  star_x i j := W.star_x _ _
  mul_x i j k l := by simp only [W.mul_x,EmbeddingLike.apply_eq_iff_eq]
  diagonal := (Equiv.sum_comp e.symm (fun i=>W.x i i)).trans W.diagonal

variable [instNontrivialA : Nontrivial A]
omit instSize instPauliData instNontrivialA in
lemma pure_full
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type u}
    {B : Type u}
    [CStarAlgebra A]
    [CStarAlgebra B]
    [PartialOrder A]
    [StarOrderedRing A]
    [PartialOrder B]
    [StarOrderedRing B]
    [Nontrivial A]
    {a : A} {b : B} (ha : IsFull a) (hb : IsFull b) : IsFull (pure a b) := by
  classical
  obtain ⟨n,h,l,h1⟩ := FullComparison.finite_presentation ha
  obtain ⟨m,s,t,h2⟩ := FullComparison.finite_presentation hb
  let K := TwoSidedIdeal.span ({pure a b} : Set (Algebra A B))
  apply TwoSidedIdeal.eq_top
  have he : (∑ i : Fin n, ∑ j : Fin m, pure (h i) (s j)*pure a b*pure (l i) (t j))=1 := by
    simp only [pure_mul]
    simp_rw [← pure_sum_right]
    rw [← pure_sum_left,h1,h2,pure_one]
  rw [← he]
  apply K.asIdeal.sum_mem
  intro i hi
  apply K.asIdeal.sum_mem
  intro j hj
  exact K.mul_mem_right _ _ (K.mul_mem_left _ _ (TwoSidedIdeal.subset_span (by simp)))
end KirchbergRordam.GenericRW.FullRankWeighted

namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open OrderZero
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {w : A} (hw : w * w = 0)
omit hw in
omit instSize instPauliData in
lemma abs_mul_self_zero.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {w : A}
    (hw : w * w = 0)
    : CFC.sqrt (star w * w) * w = 0 := by
  apply Intertwining.sqrt_mul_eq_zero (star_mul_self_nonneg w)
  rw [mul_assoc, hw, mul_zero]

omit hw in
omit instSize instPauliData in
lemma self_mul_coabs_zero.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {w : A}
    (hw : w * w = 0)
    : w * CFC.sqrt (w * star w) = 0 := by
  apply Intertwining.mul_sqrt_eq_zero (mul_star_self_nonneg w)
  rw [← mul_assoc, hw, zero_mul]

include hw in
lemma abs_coabs_zero : CFC.sqrt (star w * w) * CFC.sqrt (w * star w) = 0 := by
  apply Intertwining.mul_sqrt_eq_zero (mul_star_self_nonneg w)
  rw [← mul_assoc, abs_mul_self_zero hw, zero_mul]

omit instSize instPauliData in
lemma self_abs.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {w : A}
    : w * CFC.sqrt (star w * w) = CFC.sqrt (w * star w) * w :=
  Intertwining.sqrt (star_mul_self_nonneg w) (mul_star_self_nonneg w) (mul_assoc _ _ _).symm


def ofSquareZero (hw : w * w = 0) (hn : ‖w‖ ≤ 1) : WeightedUnits (Fin 2) A := by
  let a := CFC.sqrt (star w * w)
  let b := CFC.sqrt (w * star w)
  let x : Fin 2 → Fin 2 → A := ![![a, star w], ![w, b]]
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hb : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have haa : a * a = star w * w := CFC.sqrt_mul_sqrt_self _
  have hbb : b * b = w * star w := CFC.sqrt_mul_sqrt_self _
  have hab : a * b = 0 := abs_coabs_zero hw
  have hba : b * a = 0 := by simpa only [star_mul, ha.star_eq, hb.star_eq, star_zero] using congrArg star hab
  have haw : a * w = 0 := abs_mul_self_zero hw
  have hwb : w * b = 0 := self_mul_coabs_zero hw
  have hwa : w * a = b * w := self_abs
  have hwsa : star w * a = 0 := by simpa only [star_mul, ha.star_eq, star_zero] using congrArg star haw
  have hbws : b * star w = 0 := by simpa only [star_mul, hb.star_eq, star_zero] using congrArg star hwb
  have hbw : a * star w = star w * b := by
    simpa only [star_mul, ha.star_eq, hb.star_eq] using congrArg star hwa
  have hws : star w * star w = 0 := by simpa only [star_mul, star_zero] using congrArg star hw
  refine ⟨a + b, x, add_nonneg (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _), ?_, ?_, ?_, by simp [Fin.sum_univ_two, x]⟩
  · rw [ha.norm_add_eq_max hb hab]
    dsimp only [a, b]
    rw [CFC.norm_sqrt (star w * w), CFC.norm_sqrt (w * star w), CStarRing.norm_star_mul_self, CStarRing.norm_self_mul_star,
      Real.sqrt_mul_self (norm_nonneg _), max_self]
    exact hn
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [x, ha.star_eq, hb.star_eq]
  · intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [x, add_mul, haa, hbb, hab, hba, haw, hwb, hwsa, hbws, hws, hw, hwa, hbw]


end KirchbergRordam.GenericRW.FullRankWeighted

namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor OrderZero Fullness
universe u
variable {P : Type u} [CStarAlgebra P]
local instance (n : ℕ) : PartialOrder (powerPack P n) := CStarAlgebra.spectralOrder _
local instance (n : ℕ) : StarOrderedRing (powerPack P n) := CStarAlgebra.spectralOrderedRing _
local instance : PartialOrder P := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing P := CStarAlgebra.spectralOrderedRing _

abbrev Row := KirchbergRordam.PauliPower.Row

def power (W : WeightedUnits (Fin 2) P) : (k : ℕ) → WeightedUnits (Row k) (powerPack P k)
  | 0 => W
  | k+1 => tensor W (power W k)

variable [Nontrivial P]
lemma power_full (W : WeightedUnits (Fin 2) P) (hW : ∀ i, IsFull (W.x i i))
    (k : ℕ) (i : Row k) : IsFull ((power W k).x i i) := by
  induction k with
  | zero => exact hW i
  | succ k ih => exact pure_full (hW i.1) (ih i.2)

omit instSize instPauliData in
lemma exists_flatten
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (D : Type u) [CStarAlgebra D] (n k : ℕ) :
    ∃ m : ℕ, Nonempty (powerPack (powerPack D n) k →⋆ₐ[ℂ] powerPack D m) := by
  induction k with
  | zero => exact ⟨n,⟨StarAlgHom.id ℂ _⟩⟩
  | succ k ih =>
    obtain ⟨m,⟨φ⟩⟩ := ih
    obtain ⟨ψ⟩ := exists_joinPower D n m
    exact ⟨n+m+1,⟨ψ.comp (MaxTensor.map (StarAlgHom.id ℂ (powerPack D n)) φ)⟩⟩
end KirchbergRordam.GenericRW.FullRankWeighted

namespace KirchbergRordam.GenericRW.FullRankWeighted
section
open OrderZero Fullness _root_.OAI.KirchbergRordam.GenericRW.MaxTensor
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [instNontrivialA : Nontrivial A]
omit instSize instPauliData in
lemma sqrt_star_mul_self_full.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    [instNontrivialA : Nontrivial A]
    {w : A} (hw : IsFull w) : IsFull (CFC.sqrt (star w*w)) := by
  apply full_of_survives
  intro π he
  have hh := congrArg π.representation (CFC.sqrt_mul_sqrt_self (star w*w))
  rw [map_mul,he,zero_mul,map_mul,map_star] at hh
  exact full_survives hw π.representation ((CStarRing.star_mul_self_eq_zero_iff _).mp hh.symm)
omit instSize instPauliData in
lemma sqrt_mul_star_self_full.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    [instNontrivialA : Nontrivial A]
    {w : A} (hw : IsFull w) : IsFull (CFC.sqrt (w*star w)) := by
  apply full_of_survives
  intro π he
  have hh := congrArg π.representation (CFC.sqrt_mul_sqrt_self (w*star w))
  rw [map_mul,he,zero_mul,map_mul,map_star] at hh
  exact full_survives hw π.representation ((CStarRing.mul_star_self_eq_zero_iff _).mp hh.symm)

lemma ofSquareZero_full {w : A} (hw : w*w=0) (hn : ‖w‖≤1) (hf : IsFull w) (i : Fin 2) :
    IsFull ((ofSquareZero hw hn).x i i) := by
  fin_cases i
  · exact sqrt_star_mul_self_full hf
  · exact sqrt_mul_star_self_full hf
end

open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor Fullness
universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]
omit [Size] [PauliData] in
theorem exists_full_cone (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) (k : ℕ) :
    ∃ m : ℕ, ∃ η : @ConeModel.Cone (powerSize k) →⋆ₐ[ℂ] powerPack D m,
      IsFull (η (@ConeModel.corner (powerSize k) 0 0)) := by
  let : Size := powerSize k
  let : PauliData := powerPauliData k
  obtain ⟨n,y,hyz,hyfull⟩ := FullSquareZero.exists_full_square_zero hD
  obtain ⟨w,hwz,hwfull,hwn⟩ := FullSquareZero.normalize hyz hyfull
  let := CStarAlgebra.spectralOrder (powerPack D n)
  let := CStarAlgebra.spectralOrderedRing (powerPack D n)
  let W := ofSquareZero hwz hwn.le
  let := CStarAlgebra.spectralOrder (powerPack (powerPack D n) k)
  let := CStarAlgebra.spectralOrderedRing (powerPack (powerPack D n) k)
  let V := reindex (power W k) (rowEquiv k)
  obtain ⟨m,⟨φ⟩⟩ := exists_flatten D n k
  let := CStarAlgebra.spectralOrder (powerPack D m)
  let := CStarAlgebra.spectralOrderedRing (powerPack D m)
  let R := V.map φ
  refine ⟨m,R.coneHom,?_⟩
  rw [R.coneHom_corner]
  apply Fullness.full_map
  exact power_full W (ofSquareZero_full hwz hwn.le hwfull) k ((rowEquiv k).symm 0)
end KirchbergRordam.GenericRW.FullRankWeighted

namespace KirchbergRordam.GenericRW.ConeCut
lemma q_zero_eq_corner : q 0 (le_refl 0)=ConeModel.corner 0 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [ConeModel.corner_apply]
  change coeff 0 t • unit 0 0=(↑(t:ℝ):ℂ) • CStarMatrix.ofMatrix (Matrix.single 0 0 1)
  rw [show coeff 0 t=(t:ℝ) by simp [coeff,max_eq_left t.property.1]]
  exact (Complex.coe_smul _ _).symm
end KirchbergRordam.GenericRW.ConeCut

namespace KirchbergRordam.GenericRW
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor
omit [Size] [PauliData] in


theorem finite_prime_power_drop (D : Type*) [CStarAlgebra D] [Nontrivial D]
    (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) (k : ℕ) :
    ∃ m : ℕ, Nonempty (@DimensionDrop23 (powerSize k) →⋆ₐ[ℂ] powerPack D m) := by
  let : Size := powerSize k
  let : PauliData := powerPauliData k
  obtain ⟨n,η,hη⟩ := FullRankWeighted.exists_full_cone hD k
  let := CStarAlgebra.spectralOrder (powerPack D n)
  let := CStarAlgebra.spectralOrderedRing (powerPack D n)
  obtain ⟨l,⟨φ⟩⟩ := ConeDrop.exists_drop_from_full_cone η (by rwa [ConeCut.q_zero_eq_corner])
  obtain ⟨m,⟨ψ⟩⟩ := FullRankWeighted.exists_flatten D n l
  exact ⟨m,⟨ψ.comp φ⟩⟩
end KirchbergRordam.GenericRW

omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
end

end OAI
