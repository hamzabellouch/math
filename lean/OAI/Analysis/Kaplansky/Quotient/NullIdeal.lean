import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions
import OAI.Analysis.Kaplansky.Quotient.ClosedStarQuotient

namespace OAI

noncomputable section


namespace KaplanskyConsequences
open scoped Matrix CStarAlgebra ComplexOrder
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
abbrev Mat (A : Type*) (n : ℕ) := CStarMatrix (Fin n) (Fin n) A

private local instance matRealCFC (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (Mat A n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

private local instance matNonnegSpectrum (n : ℕ) : NonnegSpectrumClass ℝ (Mat A n) :=
  CStarAlgebra.instNonnegSpectrumClass

namespace SpectralKernel
variable (d : CuntzDimensionState A)

abbrev val {n : ℕ} (a : Mat A n) : ℝ := d.signedValue a

lemma val_of_nonneg {n : ℕ} {a : Mat A n} (ha : 0 ≤ a) :
    val d a = d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ :=
  d.signedValue_of_nonneg ha

@[simp] lemma val_zero (n : ℕ) : val d (0 : Mat A n) = 0 := d.signedValue_zero n

lemma val_nonneg {n : ℕ} {a : Mat A n} (ha : 0 ≤ a) : 0 ≤ val d a := by
  rw [val_of_nonneg d ha]
  exact d.spectralValue_nonneg _

lemma val_mono {n : ℕ} {a b : Mat A n} (ha : 0 ≤ a) (hab : a ≤ b) :
    val d a ≤ val d b := by
  rw [val_of_nonneg d ha, val_of_nonneg d (ha.trans hab)]
  exact d.spectralValue_mono_positive ha (ha.trans hab) hab

@[simp] lemma val_one (n : ℕ) : val d (1 : Mat A n) = n := by
  rw [val_of_nonneg d zero_le_one]
  exact d.spectralValue_unit n

lemma val_smul {n : ℕ} (r : ℝ) (a : Mat A n) : val d (r • a) = r * val d a :=
  d.signedValue_smul a r

lemma val_shift {n : ℕ} {a : Mat A n} (ha : 0 ≤ a) {r : ℝ} (hr : 0 ≤ r) :
    val d (a + r • 1) = val d a + r*n := by
  rw [val_of_nonneg d (add_nonneg ha (smul_nonneg hr zero_le_one)), val_of_nonneg d ha]
  exact d.spectralValue_shift ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ r hr

lemma val_square_swap {n : ℕ} (x : Mat A n) :
    val d (x*star x) = val d (star x*x) := by
  rw [val_of_nonneg d (mul_star_self_nonneg x), val_of_nonneg d (star_mul_self_nonneg x)]
  exact d.spectralValue_square_swap x

lemma abs_val_sub_le {n : ℕ} {a b : Mat A n} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |val d a - val d b| ≤ ‖a-b‖ * n := by
  rw [val_of_nonneg d ha, val_of_nonneg d hb]
  exact d.abs_spectralValue_sub_le ha hb

lemma mat_sum_apply {m n ι : Type*} (s : Finset ι) (f : ι → CStarMatrix m n A)
    (i : m) (j : n) : (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert, ha, ih]

lemma gram_nonneg {m n : Type*} [Fintype m] [Fintype n] (x : Matrix m n A) :
    0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x) := by
  classical
  by_cases hn : Nonempty n
  · let i₀ : n := Classical.choice hn
    let y (k : m) : CStarMatrix n n A := CStarMatrix.ofMatrix fun i j => if i = i₀ then x k j else 0
    have he : CStarMatrix.ofMatrix (x.conjTranspose*x) = ∑ k, star (y k)*y k := by
      ext i j
      simp only [CStarMatrix.ofMatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        mat_sum_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply]
      apply Finset.sum_congr rfl
      intro k hk
      change star (x k i) * x k j =
        ∑ l, star (if l = i₀ then x k i else 0) * (if l = i₀ then x k j else 0)
      simp
    rw [he]
    exact Finset.sum_nonneg fun k _ => star_mul_self_nonneg _
  · have : IsEmpty n := not_nonempty_iff.mp hn
    have he : CStarMatrix.ofMatrix (x.conjTranspose*x) = 0 := by ext i; exact isEmptyElim i
    rw [he]

lemma gram_swap {n m : ℕ} (x : Matrix (Fin n) (Fin m) A) :
    val d (CStarMatrix.ofMatrix (x*x.conjTranspose)) =
      val d (CStarMatrix.ofMatrix (x.conjTranspose*x)) := by
  have hx := gram_nonneg x.conjTranspose
  rw [Matrix.conjTranspose_conjTranspose] at hx
  rw [val_of_nonneg d hx, val_of_nonneg d (gram_nonneg x)]
  exact d.spectralValue_rectangular_gram x hx (gram_nonneg x)

private lemma weighted_gram_identity {n : ℕ} (a b S T : Mat A n) (r : ℝ)
    (hr : r ≠ 0) (hS : star S = S) (hT : star T = T) (hSS : S*S=a) (hTT : T*T=b) :
    let v := Matrix.fromCols (CStarMatrix.ofMatrix.symm S) (CStarMatrix.ofMatrix.symm T)
    let w := Matrix.fromCols (CStarMatrix.ofMatrix.symm (r • S))
      (CStarMatrix.ofMatrix.symm (-(r⁻¹ • T)))
    v.conjTranspose*v + w.conjTranspose*w =
      cuntzBlock (CStarMatrix.ofMatrix.symm ((1+r^2) • a))
        (CStarMatrix.ofMatrix.symm ((1+r⁻¹^2) • b)) := by
  let v := Matrix.fromCols (CStarMatrix.ofMatrix.symm S) (CStarMatrix.ofMatrix.symm T)
  let w := Matrix.fromCols (CStarMatrix.ofMatrix.symm (r • S))
    (CStarMatrix.ofMatrix.symm (-(r⁻¹ • T)))
  have hm : v.conjTranspose*v + w.conjTranspose*w =
      cuntzBlock (CStarMatrix.ofMatrix.symm ((1+r^2) • a))
        (CStarMatrix.ofMatrix.symm ((1+r⁻¹^2) • b)) := by
    dsimp [v,w]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols]
    rw [Matrix.fromBlocks_add]
    congr 1
    · change star S*S + star (r • S)*(r • S) = (1+r^2) • a
      simp [hS,hSS,smul_smul,pow_two,add_smul]
    · change star S*T + star (r • S)*(-(r⁻¹ • T)) = 0
      simp [hS,smul_smul,hr]
    · change star T*S + star (-(r⁻¹ • T))*(r • S) = 0
      simp [hT,smul_smul,hr]
    · change star T*T + star (-(r⁻¹ • T))*(-(r⁻¹ • T)) = (1+r⁻¹^2) • b
      simp [hT,hTT,smul_smul,pow_two,add_smul]
  exact hm

lemma val_add_le {n : ℕ} {a b : Mat A n} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (r : ℝ) (hr : r ≠ 0) :
    val d (a+b) ≤ (1+r^2)*val d a + (1+r⁻¹^2)*val d b := by
  let S := CFC.sqrt a
  let T := CFC.sqrt b
  have hS : star S = S := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have hT : star T = T := (CFC.sqrt_nonneg b).isSelfAdjoint.star_eq
  have hSS : S*S = a := CFC.sqrt_mul_sqrt_self a ha
  have hTT : T*T = b := CFC.sqrt_mul_sqrt_self b hb
  let v := Matrix.fromCols (CStarMatrix.ofMatrix.symm S) (CStarMatrix.ofMatrix.symm T)
  let w := Matrix.fromCols (CStarMatrix.ofMatrix.symm (r • S))
    (CStarMatrix.ofMatrix.symm (-(r⁻¹ • T)))
  have hv : v*v.conjTranspose = CStarMatrix.ofMatrix.symm (a+b) := by
    dsimp [v]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]
    change S*star S + T*star T = a+b
    rw [hS,hT,hSS,hTT]
  have hm := weighted_gram_identity a b S T r hr hS hT hSS hTT
  let v' := v.submatrix (Equiv.refl _) finSumFinEquiv.symm
  let w' := w.submatrix (Equiv.refl _) finSumFinEquiv.symm
  let p : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm ((1+r^2) • a),
    smul_nonneg (show (0:ℝ) ≤ 1+r^2 by positivity) ha⟩
  let q : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm ((1+r⁻¹^2) • b),
    smul_nonneg (show (0:ℝ) ≤ 1+r⁻¹^2 by positivity) hb⟩
  have hv' : CStarMatrix.ofMatrix (v'*v'.conjTranspose) = a+b := by
    dsimp [v']
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hv]
    rfl
  have hm' : CStarMatrix.ofMatrix (v'.conjTranspose*v') +
      CStarMatrix.ofMatrix (w'.conjTranspose*w') = CStarMatrix.ofMatrix (p.add q).matrix := by
    dsimp [v',w',p,q,CuntzPositiveMatrix.add]
    simp only [Matrix.conjTranspose_submatrix]
    change CStarMatrix.ofMatrix ((v.conjTranspose*v + w.conjTranspose*w).submatrix _ _) = _
    rw [hm]
    rfl
  have hle : CStarMatrix.ofMatrix (v'.conjTranspose*v') ≤
      CStarMatrix.ofMatrix (p.add q).matrix := by
    rw [← hm']
    exact le_add_of_nonneg_right (gram_nonneg w')
  have h := val_mono d (gram_nonneg v') hle
  rw [← gram_swap d v', hv'] at h
  have h := h.trans_eq (val_of_nonneg d (p.add q).nonneg)
  change val d (a+b) ≤ d.spectralValue (p.add q) at h
  rw [d.spectralValue_add p q] at h
  have hp := val_of_nonneg d (smul_nonneg (show (0:ℝ) ≤ 1+r^2 by positivity) ha)
  have hq := val_of_nonneg d (smul_nonneg (show (0:ℝ) ≤ 1+r⁻¹^2 by positivity) hb)
  change val d ((1+r^2) • a) = d.spectralValue p at hp
  change val d ((1+r⁻¹^2) • b) = d.spectralValue q at hq
  rw [← hp, ← hq, val_smul, val_smul] at h
  exact h

lemma val_add_of_zero {n : ℕ} {a b : Mat A n} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzero : val d b = 0) : val d (a+b) = val d a := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hpos : 0 < val d a+1 := by linarith [val_nonneg d ha]
    let r := Real.sqrt (ε/(val d a+1))
    have hr : 0 < r := Real.sqrt_pos.2 (div_pos hε hpos)
    have hrsq : r^2 = ε/(val d a+1) := Real.sq_sqrt (le_of_lt (div_pos hε hpos))
    have hmul : r^2*(val d a+1)=ε := by rw [hrsq]; exact div_mul_cancel₀ ε hpos.ne'
    have h := val_add_le d ha hb r hr.ne'
    rw [hzero,mul_zero,add_zero] at h
    nlinarith [sq_nonneg r]
  · exact val_mono d ha (le_add_of_nonneg_right hb)

abbrev IsNull {n : ℕ} (x : Mat A n) : Prop := val d (star x*x) = 0

lemma null_zero (n : ℕ) : IsNull d (0 : Mat A n) := by simp [IsNull]

lemma null_star {n : ℕ} {x : Mat A n} (hx : IsNull d x) : IsNull d (star x) := by
  simpa only [IsNull,star_star,val_square_swap] using hx

lemma null_add {n : ℕ} {x y : Mat A n} (hx : IsNull d x) (hy : IsNull d y) :
    IsNull d (x+y) := by
  have hab : val d (star x*x + star y*y) = 0 := by
    rw [val_add_of_zero d (star_mul_self_nonneg x) (star_mul_self_nonneg y) hy]
    exact hx
  have hle : star (x+y)*(x+y) ≤ (2 : ℝ) • (star x*x + star y*y) := by
    rw [← sub_nonneg]
    convert star_mul_self_nonneg (x-y) using 1
    simp only [two_smul,star_sub,star_add]
    noncomm_ring
  apply le_antisymm _ (val_nonneg d (star_mul_self_nonneg _))
  calc val d (star (x+y)*(x+y)) ≤ val d ((2:ℝ) • (star x*x + star y*y)) :=
        val_mono d (star_mul_self_nonneg _) hle
    _ = 0 := by rw [val_smul,hab,mul_zero]

lemma null_smul {n : ℕ} {x : Mat A n} (hx : IsNull d x) (r : ℂ) :
    IsNull d (r • x) := by
  have h : star (r • x)*(r • x) = Complex.normSq r • (star x*x) := by
    rw [star_smul,smul_mul_assoc,mul_smul_comm,smul_smul]
    change ((starRingEnd ℂ) r * r) • (star x*x) = Complex.normSq r • (star x*x)
    rw [← Complex.normSq_eq_conj_mul_self]
    exact Complex.coe_smul _ _
  dsimp [IsNull]
  rw [h,val_smul,hx,mul_zero]

lemma null_mul_left {n : ℕ} {x : Mat A n} (hx : IsNull d x) (a : Mat A n) :
    IsNull d (a*x) := by
  have hle : star (a*x)*(a*x) ≤ ‖a‖^2 • (star x*x) := by
    have h := star_left_conjugate_le_conjugate
      (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := a)) x
    simp only [mul_assoc,Algebra.algebraMap_eq_smul_one,mul_smul_comm,
      smul_mul_assoc,one_mul] at h
    simp only [star_mul, mul_assoc]
    exact h
  apply le_antisymm _ (val_nonneg d (star_mul_self_nonneg _))
  calc val d (star (a*x)*(a*x)) ≤ val d (‖a‖^2 • (star x*x)) :=
        val_mono d (star_mul_self_nonneg _) hle
    _ = 0 := by rw [val_smul,hx,mul_zero]

lemma null_mul_right {n : ℕ} {x : Mat A n} (hx : IsNull d x) (a : Mat A n) :
    IsNull d (x*a) := by
  simpa only [star_mul,star_star] using null_star d (null_mul_left d (null_star d hx) (star a))

lemma continuous_squareVal (n : ℕ) : Continuous (fun x : Mat A n => val d (star x*x)) := by
  have hc : Continuous (fun x : Mat A n =>
      (⟨star x*x,star_mul_self_nonneg x⟩ : {a : Mat A n // 0 ≤ a})) :=
    (continuous_star.mul continuous_id).subtype_mk _
  simpa only [Function.comp_def,val_of_nonneg d (star_mul_self_nonneg _)] using
    (d.spectralValue_continuous n).comp hc

def nullIdeal (n : ℕ) : ClosedStarIdeal (Mat A n) where
  carrier := {x | IsNull d x}
  zero_mem' := null_zero d n
  add_mem' := null_add d
  smul_mem' := fun r _ hx => null_smul d hx r
  mul_mem' := fun _ hy => null_mul_left d hy _
  star_mem' := null_star d
  mul_mem_left := fun a _ hx => null_mul_left d hx a
  mul_mem_right := fun _ a hx => null_mul_right d hx a
  closed := isClosed_eq (continuous_squareVal d n) continuous_const

lemma val_zero_of_null {n : ℕ} {a : Mat A n} (ha : 0 ≤ a) (hx : IsNull d a) :
    val d a = 0 := by
  have hs : CFC.sqrt a ∈ (nullIdeal d n).toNonUnitalStarSubalgebra := by
    rw [CFC.sqrt_eq_real_sqrt a ha]
    exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt hx
  change IsNull d (CFC.sqrt a) at hs
  simpa only [IsNull,(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self a ha] using hs

lemma null_of_val_zero {n : ℕ} {a : Mat A n} (ha : 0 ≤ a) (hx : val d a = 0) :
    IsNull d a := by
  have hs : IsNull d (CFC.sqrt a) := by
    simpa only [IsNull,(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq,
      CFC.sqrt_mul_sqrt_self a ha] using hx
  simpa only [CFC.sqrt_mul_sqrt_self a ha] using null_mul_left d hs (CFC.sqrt a)

lemma null_posPart {n : ℕ} {a : Mat A n} (hx : IsNull d a) : IsNull d a⁺ := by
  change a⁺ ∈ (nullIdeal d n).toNonUnitalStarSubalgebra
  exact cfcₙ_mem (𝕜' := ℂ) (fun t : ℝ => max t 0) hx

lemma null_sub {n : ℕ} {a b : Mat A n} (ha : IsNull d a) (hb : IsNull d b) :
    IsNull d (a-b) := (nullIdeal d n).submodule.sub_mem ha hb

lemma val_eq_of_null_sub {n : ℕ} {a b : Mat A n} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : IsNull d (a-b)) : val d a = val d b := by
  have haux {a b : Mat A n} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : IsNull d (a-b)) :
      val d a ≤ val d b := by
    have hle : a ≤ b+(a-b)⁺ := by
      have hp := CFC.le_posPart (ha.isSelfAdjoint.sub hb.isSelfAdjoint)
      exact (sub_le_iff_le_add'.1 hp)
    calc val d a ≤ val d (b+(a-b)⁺) := val_mono d ha hle
      _ = val d b := val_add_of_zero d hb (CFC.posPart_nonneg _)
        (val_zero_of_null d (CFC.posPart_nonneg _) (null_posPart d hab))
  exact le_antisymm (haux ha hb hab) (haux hb ha (by
    have h := (nullIdeal d n).submodule.neg_mem hab
    change IsNull d (-(a-b)) at h
    simpa only [neg_sub] using h))

lemma val_scalar_sub {n : ℕ} {a : Mat A n} (ha : IsSelfAdjoint a) (r : ℝ) :
    val d (r • 1 - a) = r*n - val d a := by
  let : IsStarNormal a := ha.isStarNormal
  let S := StarAlgebra.elemental ℂ a
  let : CommCStarAlgebra S := inferInstance
  let x : S := ⟨a,StarAlgebra.elemental.self_mem ℂ a⟩
  let φ : S →⋆ₐ[ℂ] Mat A n := S.subtype
  let f := d.commutativeValueLinearMap φ
  have h := f.map_sub ((r:ℂ) • (1:S)) x
  rw [f.map_smul] at h
  dsimp [f] at h
  simp only [CuntzDimensionState.commutativeValueLinearMap_apply] at h
  change d.complexValue ((r:ℂ) • (1:Mat A n) - a) =
    (r:ℂ) * d.complexValue (1:Mat A n) - d.complexValue a at h
  rw [Complex.coe_smul, d.complexValue_one, d.complexValue_selfAdjoint ha] at h
  have he := d.complexValue_selfAdjoint
    (((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one (Mat A n))).sub ha)
  have h := he.symm.trans h
  exact_mod_cast h

end SpectralKernel
end KaplanskyConsequences

end

end OAI
