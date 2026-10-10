import OAI.InformationTheory.AmplitudeDamping.TensorEntropy

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} [Fintype ι]

def vecMass (ψ : ι → ℂ) : ℝ := ∑ i, Complex.normSq (ψ i)

theorem vecMass_nonneg (ψ : ι → ℂ) : 0 ≤ vecMass ψ :=
  Finset.sum_nonneg (fun i _ ↦ Complex.normSq_nonneg (ψ i))

theorem pure_posSemidef (ψ : ι → ℂ) : (pure ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star ψ

theorem pure_trace (ψ : ι → ℂ) : (pure ψ).trace = (vecMass ψ : ℂ) := by
  simp [Matrix.trace, pure, vecMass, Complex.mul_conj]

theorem pure_state [DecidableEq ι] {ψ : ι → ℂ} (hψ : vecMass ψ = 1) : IsState (pure ψ) := by
  exact ⟨pure_posSemidef ψ, by rw [pure_trace,hψ]; rfl⟩

theorem vecMass_eq_zero {ψ : ι → ℂ} : vecMass ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    funext i
    apply Complex.normSq_eq_zero.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ Complex.normSq_nonneg (ψ i))).mp h i
      (Finset.mem_univ i)
  · rintro rfl
    simp [vecMass]

variable [DecidableEq ι]

def unitVec [Inhabited ι] : ι → ℂ := fun i ↦ if i = default then 1 else 0

@[simp] theorem vecMass_unitVec [Inhabited ι] : vecMass (unitVec (ι := ι)) = 1 := by
  simp [vecMass, unitVec]

omit [DecidableEq ι] in
theorem vecMass_smul (z : ℂ) (ψ : ι → ℂ) :
    vecMass (z • ψ) = Complex.normSq z * vecMass ψ := by
  simp [vecMass, Complex.normSq_mul, Finset.mul_sum]

def normalize [Inhabited ι] (ψ : ι → ℂ) : ι → ℂ :=
  if vecMass ψ = 0 then unitVec else ((Real.sqrt (vecMass ψ) : ℂ)⁻¹) • ψ

theorem sqrt_mass_normalize [Inhabited ι] (ψ : ι → ℂ) :
    (Real.sqrt (vecMass ψ) : ℂ) • normalize ψ = ψ := by
  by_cases h : vecMass ψ = 0
  · have hz := vecMass_eq_zero.mp h
    simp [normalize,hz,vecMass]
  · have hs : (Real.sqrt (vecMass ψ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (vecMass_nonneg ψ) (Ne.symm h)))
    simp [normalize,h,smul_smul,hs]

theorem normalize_mass [Inhabited ι] (ψ : ι → ℂ) : vecMass (normalize ψ) = 1 := by
  by_cases h : vecMass ψ = 0
  · simp [normalize,h]
  · have hs : Real.sqrt (vecMass ψ)*Real.sqrt (vecMass ψ) = vecMass ψ := Real.mul_self_sqrt (vecMass_nonneg ψ)
    simp only [normalize, ite_eq_right h, vecMass_smul, map_inv₀, Complex.normSq_ofReal, hs]
    exact inv_mul_cancel₀ h

theorem normSq_normalize [Inhabited ι] (ψ : ι → ℂ) (i : ι) :
    Complex.normSq (ψ i) = vecMass ψ * Complex.normSq (normalize ψ i) := by
  calc
    Complex.normSq (ψ i) = Complex.normSq (((Real.sqrt (vecMass ψ) : ℂ) • normalize ψ) i) :=
      congrArg (fun f : ι → ℂ ↦ Complex.normSq (f i)) (sqrt_mass_normalize ψ).symm
    _ = _ := by simp [Complex.normSq_mul, Real.mul_self_sqrt (vecMass_nonneg ψ)]

end

section
open scoped BigOperators ComplexOrder
open Matrix

def branch {n : ℕ} (ψ : Basis (n+1) → ℂ) (b : Fin 2) : Basis n → ℂ :=
  fun i ↦ ψ (Fin.cons b i)

def population {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) : ℝ :=
  ∑ i, if i j = 1 then Complex.normSq (ψ i) else 0

theorem population_nonneg {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    0 ≤ population ψ j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact Complex.normSq_nonneg _
  · rfl

theorem population_le_mass {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    population ψ j ≤ vecMass ψ := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · rfl
  · exact Complex.normSq_nonneg _

theorem population_mem {n : ℕ} {ψ : Basis n → ℂ} (hψ : vecMass ψ = 1) (j : Fin n) :
    population ψ j ∈ Set.Icc (0:ℝ) 1 :=
  ⟨population_nonneg ψ j, hψ ▸ population_le_mass ψ j⟩

theorem vecMass_branches {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    vecMass ψ = vecMass (branch ψ 0) + vecMass (branch ψ 1) := by
  unfold vecMass
  rw [sum_fin_cons]
  simp [Fin.sum_univ_two,branch]

theorem population_zero {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    population ψ 0 = vecMass (branch ψ 1) := by
  unfold population
  rw [sum_fin_cons]
  simp [vecMass,branch]

theorem population_succ {n : ℕ} (ψ : Basis (n+1) → ℂ) (j : Fin n) :
    population ψ j.succ = population (branch ψ 0) j + population (branch ψ 1) j := by
  unfold population
  rw [sum_fin_cons]
  simp [Fin.sum_univ_two,branch]

theorem population_normalize {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    population ψ j = vecMass ψ * population (normalize ψ) j := by
  simp only [population,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · exact normSq_normalize ψ i
  · exact (mul_zero _).symm

def basisSplit (n : ℕ) : Basis n ⊕ Basis n ≃ Basis (n+1) where
  toFun := Sum.elim (fun i : Basis n ↦ Fin.cons 0 i) (fun i : Basis n ↦ Fin.cons 1 i)
  invFun i := if i 0 = 0 then Sum.inl (Fin.tail i) else Sum.inr (Fin.tail i)
  left_inv i := by cases i <;> simp
  right_inv i := by
    have h := Fin.cons_self_tail i
    have hi : i 0 = 0 ∨ i 0 = 1 := by have := (i 0).isLt; omega
    rcases hi with hi | hi <;> simp [hi] at * <;> exact h

@[simp] theorem basisSplit_inl {n : ℕ} (i : Basis n) : basisSplit n (Sum.inl i) = Fin.cons 0 i := rfl
@[simp] theorem basisSplit_inr {n : ℕ} (i : Basis n) : basisSplit n (Sum.inr i) = Fin.cons 1 i := rfl

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem channel_pure_apply (γ ν : ℝ) (n : ℕ) (ψ : Basis n → ℂ) (i j : Basis n) :
    channel γ ν n (pure ψ) i j =
      ∑ r, (tensorKraus γ ν n r *ᵥ ψ) i * star ((tensorKraus γ ν n r *ᵥ ψ) j) := by
  simp only [channel,mul_pure_mul_conjTranspose,Matrix.sum_apply,pure]

theorem tensorKraus_mulVec_cons (γ ν : ℝ) {n : ℕ} (r : Fin 4) (R : Fin n → Fin 4)
    (ψ : Basis (n+1) → ℂ) (b : Fin 2) (i : Basis n) :
    (tensorKraus γ ν (n+1) (Fin.cons r R) *ᵥ ψ) (Fin.cons b i) =
      ∑ a : Fin 2, kraus γ ν r b a * (tensorKraus γ ν n R *ᵥ branch ψ a) i := by
  simp only [Matrix.mulVec,dotProduct]
  rw [sum_fin_cons]
  simp only [tensorKraus,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  simp only [branch,Finset.mul_sum,mul_assoc]

theorem channel_first_site_entry (γ ν : ℝ) {n : ℕ} (ψ : Basis (n+1) → ℂ)
    (b c : Fin 2) (i j : Basis n) :
    channel γ ν (n+1) (pure ψ) (Fin.cons b i) (Fin.cons c j) =
      applyKraus (kraus γ ν)
        (fun a d ↦ (columns (tensorKraus γ ν n) (branch ψ a) *
          (columns (tensorKraus γ ν n) (branch ψ d)).conjTranspose) i j) b c := by
  rw [channel_pure_apply,sum_fin_cons]
  simp only [tensorKraus_mulVec_cons]
  let u (R : Fin n → Fin 4) (a : Fin 2) (k : Basis n) :=
    (tensorKraus γ ν n R *ᵥ branch ψ a) k
  change (∑ r : Fin 4, ∑ R : Fin n → Fin 4,
      (∑ a : Fin 2, kraus γ ν r b a * u R a i) *
        star (∑ d : Fin 2, kraus γ ν r c d * u R d j)) =
    ∑ r : Fin 4, ∑ d : Fin 2,
      (∑ a : Fin 2, kraus γ ν r b a * (∑ R : Fin n → Fin 4, u R a i * star (u R d j))) *
        star (kraus γ ν r c d)
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro R _
  ring

theorem channel_branch_blocks (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    Matrix.reindex (basisSplit n).symm (basisSplit n).symm (channel γ ν (n+1) (pure ψ)) =
      thermal (columns (tensorKraus γ ν n) (branch ψ 0))
        (columns (tensorKraus γ ν n) (branch ψ 1))
        (1-γ*ν) (γ*(1-ν)) (γ*ν) (1-γ*(1-ν)) (Real.sqrt (1-γ)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,basisSplit_inl,basisSplit_inr,
      channel_first_site_entry]
  all_goals
    rw [local_channel γ ν hγ hν (fun a d ↦
      (columns (tensorKraus γ ν n) (branch ψ a) *
        (columns (tensorKraus γ ν n) (branch ψ d)).conjTranspose) i j)]
    simp [thermal,gram]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_2} {κ : Type u_3} {ρ : Type u_4} [Fintype ι] [Fintype κ] [Fintype ρ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]

omit [Fintype ι] [Fintype ρ] [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] in
theorem columns_smul (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) (z : ℂ) :
    columns L (z • ψ) = z • columns L ψ := by
  ext i r
  simp [columns, Matrix.mulVec_smul]

omit [Fintype ι] [Fintype ρ] [DecidableEq ι] [DecidableEq ρ] in
theorem columns_normalize [Inhabited κ] (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    columns L ψ = Real.sqrt (vecMass ψ) • columns L (normalize ψ) := by
  rw [← Complex.coe_smul, ← columns_smul, sqrt_mass_normalize]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] in
theorem gram_columns (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    gram (columns L ψ) = applyKraus L (pure ψ) := columns_pure L ψ

theorem mass_channel_columns (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (ψ : Basis n → ℂ) :
    mass (columns (tensorKraus γ ν n) ψ) = vecMass ψ := by
  unfold mass
  rw [gram_columns]
  change (channel γ ν n (pure ψ)).trace.re = _
  rw [channel_trace γ ν hγ hν, pure_trace,Complex.ofReal_re]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem thermal_sqrt_smul (X Y : Matrix ι κ ℂ) (a b c d K : ℝ)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    thermal (Real.sqrt x • X) (Real.sqrt y • Y) a b c d K =
      thermal X Y (a*x) (b*y) (c*x) (d*y) (K*Real.sqrt x*Real.sqrt y) := by
  simp only [thermal,gram_sqrt_smul hx,gram_sqrt_smul hy,smul_smul,
    Matrix.conjTranspose_smul, star_trivial,Matrix.smul_mul,Matrix.mul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

theorem channel_state (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) {P : QMatrix n} (hP : IsState P) :
    IsState (channel γ ν n P) :=
  ⟨channel_posSemidef _ _ _ hP.1, (channel_trace γ ν hγ hν n P).trans hP.2⟩

theorem output_entropy_recursion (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (ψ : Basis (n+1) → ℂ)
    (hψ : vecMass ψ = 1) :
    vecMass (branch ψ 0) * entropy (channel γ ν n (pure (normalize (branch ψ 0)))) +
      vecMass (branch ψ 1) * entropy (channel γ ν n (pure (normalize (branch ψ 1)))) +
      g (v γ ν (population ψ 0)) ≤ entropy (channel γ ν (n+1) (pure ψ)) := by
  let x := vecMass (branch ψ 0)
  let y := vecMass (branch ψ 1)
  let X := columns (tensorKraus γ ν n) (normalize (branch ψ 0))
  let Y := columns (tensorKraus γ ν n) (normalize (branch ψ 1))
  have hx : 0 ≤ x := vecMass_nonneg _
  have hy : 0 ≤ y := vecMass_nonneg _
  have hxy : x+y=1 := (vecMass_branches ψ).symm.trans hψ
  have hxy' : x=1-y := by linarith
  have hX : mass X = 1 := (mass_channel_columns γ ν hγ hν n _).trans (normalize_mass _)
  have hY : mass Y = 1 := (mass_channel_columns γ ν hγ hν n _).trans (normalize_mass _)
  have h1ν : 0 ≤ 1-ν := sub_nonneg.mpr hν.2
  have h1γ : 0 ≤ 1-γ := sub_nonneg.mpr hγ.2
  have h1γν : 0 ≤ 1-γ*ν := by nlinarith [hγ.2, mul_nonneg hγ.1 h1ν]
  have h1γν' : 0 ≤ 1-γ*(1-ν) := by nlinarith [hγ.2, mul_nonneg hγ.1 hν.1]
  have hKsq : (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y)^2 = (1-γ)*x*y := by
    rw [mul_pow,mul_pow,Real.sq_sqrt h1γ,Real.sq_sqrt hx,Real.sq_sqrt hy]
  have hh := thermal_entropy X Y hX hY
    (mul_nonneg h1γν hx) (mul_nonneg (mul_nonneg hγ.1 h1ν) hy)
    (mul_nonneg (mul_nonneg hγ.1 hν.1) hx) (mul_nonneg h1γν' hy)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    (show (1-γ*ν)*x+γ*(1-ν)*y+γ*ν*x+(1-γ*(1-ν))*y=1 by nlinarith only [hxy])
    (show ((1-γ*ν)*x)*((1-γ*(1-ν))*y)-(γ*(1-ν)*y)*(γ*ν*x)=
      (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y)^2 by rw [hKsq]; ring)
  have hcolx : (1-γ*ν)*x+γ*ν*x=x := by ring
  have hcoly : γ*(1-ν)*y+(1-γ*(1-ν))*y=y := by ring
  have hu : ((1-γ*ν)*x+γ*(1-ν)*y)*(γ*ν*x+(1-γ*(1-ν))*y)-
      (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y)^2 = v γ ν y := by
    rw [hKsq,hxy']; unfold v; ring
  have heq : Matrix.reindex (basisSplit n).symm (basisSplit n).symm
      (channel γ ν (n+1) (pure ψ)) =
        thermal X Y ((1-γ*ν)*x) (γ*(1-ν)*y) (γ*ν*x) ((1-γ*(1-ν))*y)
          (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y) := by
    rw [channel_branch_blocks γ ν hγ hν,columns_normalize _ (branch ψ 0),
      columns_normalize _ (branch ψ 1),thermal_sqrt_smul _ _ _ _ _ _ _ hx hy]
  have hent := entropy_reindex (basisSplit n).symm
    (channel_posSemidef γ ν (n+1) (pure_posSemidef ψ)).isHermitian
  rw [heq] at hent
  have hbound := hh.2.2
  rw [hcolx,hcoly,hu,hent] at hbound
  simpa only [x,y,X,Y,gram_columns,population_zero,channel,applyKraus] using hbound

end GAD

end

end OAI
