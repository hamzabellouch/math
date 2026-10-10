import OAI.InformationTheory.AmplitudeDamping.HolevoInformation

namespace OAI

noncomputable section

universe u_1 u_2 u_3

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

/-- The population-dependent lower bound for every pure input, including entangled inputs. -/
theorem pure_output_entropy_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (ψ : Basis n → ℂ)
    (hψ : vecMass ψ = 1) :
    ∑ j, g (v γ ν (population ψ j)) ≤ entropy (channel γ ν n (pure ψ)) := by
  induction n with
  | zero =>
      simpa using entropy_nonneg (channel_state γ ν hγ hν 0 (pure_state hψ))
  | succ n ih =>
      let x := vecMass (branch ψ 0)
      let y := vecMass (branch ψ 1)
      let ψ₀ := normalize (branch ψ 0)
      let ψ₁ := normalize (branch ψ 1)
      have hx : 0 ≤ x := vecMass_nonneg _
      have hy : 0 ≤ y := vecMass_nonneg _
      have hxy : x+y=1 := (vecMass_branches ψ).symm.trans hψ
      have h₀ := ih ψ₀ (normalize_mass _)
      have h₁ := ih ψ₁ (normalize_mass _)
      have hpop (j : Fin n) : population ψ j.succ = x*population ψ₀ j+y*population ψ₁ j := by
        rw [population_succ,population_normalize (branch ψ 0),population_normalize (branch ψ 1)]
      have hj (j : Fin n) : g (v γ ν (population ψ j.succ)) ≤
          x*g (v γ ν (population ψ₀ j))+y*g (v γ ν (population ψ₁ j)) := by
        rw [hpop]
        exact (convexOn_output_entropy hγ hν).2
          (population_mem (normalize_mass _) j) (population_mem (normalize_mass _) j) hx hy hxy
      calc
        ∑ j, g (v γ ν (population ψ j)) =
            g (v γ ν (population ψ 0))+∑ j : Fin n, g (v γ ν (population ψ j.succ)) :=
          Fin.sum_univ_succ _
        _ ≤ g (v γ ν (population ψ 0))+
            ∑ j : Fin n, (x*g (v γ ν (population ψ₀ j))+y*g (v γ ν (population ψ₁ j))) :=
          add_le_add le_rfl (Finset.sum_le_sum (fun j _ ↦ hj j))
        _ = g (v γ ν (population ψ 0))+
            (x*(∑ j, g (v γ ν (population ψ₀ j)))+y*(∑ j, g (v γ ν (population ψ₁ j)))) := by
          rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
        _ ≤ g (v γ ν (population ψ 0))+
            (x*entropy (channel γ ν n (pure ψ₀))+y*entropy (channel γ ν n (pure ψ₁))) :=
          add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_left h₀ hx)
            (mul_le_mul_of_nonneg_left h₁ hy))
        _ ≤ entropy (channel γ ν (n+1) (pure ψ)) := by
          have h := output_entropy_recursion γ ν hγ hν ψ hψ
          dsimp [x,y,ψ₀,ψ₁]
          linarith

theorem mixed_output_entropy_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) {P : QMatrix n} (hP : IsState P) :
    ∑ j, g (v γ ν (matrixPopulation P j)) ≤ entropy (channel γ ν n P) := by
  let w := hP.1.isHermitian.eigenvalues
  let ψ := fun a i ↦ hP.1.isHermitian.eigenvectorUnitary i a
  have hw (a) : 0 ≤ w a := hP.1.eigenvalues_nonneg a
  have hs : ∑ a, w a = 1 := spectral_weights_sum hP
  have hv (a) : vecMass (ψ a) = 1 := spectral_vectors_mass hP.1.isHermitian a
  have hdecomp : P = ∑ a, w a • pure (ψ a) := spectral_pure_decomposition hP.1.isHermitian
  have hchan : channel γ ν n P = ∑ a, w a • channel γ ν n (pure (ψ a)) := by
    rw [hdecomp,channel_mixture]
  have hpop (j) : matrixPopulation P j = ∑ a, w a * population (ψ a) j := by
    conv_lhs => rw [hdecomp]
    rw [matrixPopulation_mixture]
    simp only [matrixPopulation_pure]
  have hj (j) : g (v γ ν (matrixPopulation P j)) ≤ ∑ a, w a*g (v γ ν (population (ψ a) j)) := by
    rw [hpop]
    exact (convexOn_output_entropy hγ hν).map_sum_le (fun a _ ↦ hw a) hs
      (fun a _ ↦ population_mem (hv a) j)
  calc
    ∑ j, g (v γ ν (matrixPopulation P j)) ≤
        ∑ j, ∑ a, w a*g (v γ ν (population (ψ a) j)) :=
      Finset.sum_le_sum (fun j _ ↦ hj j)
    _ = ∑ a, w a * ∑ j, g (v γ ν (population (ψ a) j)) := by
      rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ a, w a * entropy (channel γ ν n (pure (ψ a))) :=
      Finset.sum_le_sum (fun a _ ↦ mul_le_mul_of_nonneg_left
        (pure_output_entropy_bound γ ν hγ hν n (ψ a) (hv a)) (hw a))
    _ ≤ entropy (channel γ ν n P) := by
      rw [hchan]
      exact concaveOn_entropy.le_map_sum (fun a _ ↦ hw a) hs
        (fun a _ ↦ channel_posSemidef γ ν n (pure_posSemidef (ψ a)))

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

/-- Relabeling the tensor sites. -/
def coordinatePerm {n : ℕ} {α : Type u_1} (e : Equiv.Perm (Fin n)) : (Fin n → α) ≃ (Fin n → α) where
  toFun i := i ∘ e.symm
  invFun i := i ∘ e
  left_inv i := by ext k; simp
  right_inv i := by ext k; simp

@[simp] theorem coordinatePerm_apply {n : ℕ} {α : Type u_2} (e : Equiv.Perm (Fin n))
    (i : Fin n → α) (k : Fin n) : coordinatePerm e i k = i (e.symm k) := rfl
@[simp] theorem coordinatePerm_symm_apply {n : ℕ} {α : Type u_3} (e : Equiv.Perm (Fin n))
    (i : Fin n → α) (k : Fin n) : (coordinatePerm e).symm i k = i (e k) := rfl

theorem tensorKraus_reindex (γ ν : ℝ) (n : ℕ) (e : Equiv.Perm (Fin n)) (r : Fin n → Fin 4) :
    Matrix.reindex (coordinatePerm e) (coordinatePerm e) (tensorKraus γ ν n r) =
      tensorKraus γ ν n (coordinatePerm e r) := by
  ext i j
  change (∏ k, kraus γ ν (r k) (i (e k)) (j (e k))) =
    ∏ k, kraus γ ν (r (e.symm k)) (i k) (j k)
  simpa using Equiv.prod_comp e (fun k ↦ kraus γ ν (r (e.symm k)) (i k) (j k))

theorem channel_reindex (γ ν : ℝ) (n : ℕ) (e : Equiv.Perm (Fin n)) (P : QMatrix n) :
    Matrix.reindex (coordinatePerm e) (coordinatePerm e) (channel γ ν n P) =
      channel γ ν n (Matrix.reindex (coordinatePerm e) (coordinatePerm e) P) := by
  let φ := reindexStarAlgEquiv (coordinatePerm e : Basis n ≃ Basis n)
  have hL (r : Fin n → Fin 4) : φ (tensorKraus γ ν n r) =
      tensorKraus γ ν n (coordinatePerm e r) := tensorKraus_reindex γ ν n e r
  change φ (∑ r, tensorKraus γ ν n r * P * star (tensorKraus γ ν n r)) = _
  simp only [map_sum,map_mul,map_star,hL]
  exact (coordinatePerm e : (Fin n → Fin 4) ≃ _).sum_comp
    (fun r ↦ tensorKraus γ ν n r * φ P * star (tensorKraus γ ν n r))

theorem matrixPopulation_reindex {n : ℕ} (e : Equiv.Perm (Fin n)) (P : QMatrix n) (j : Fin n) :
    matrixPopulation (Matrix.reindex (coordinatePerm e) (coordinatePerm e) P) j =
      matrixPopulation P (e.symm j) := by
  apply Fintype.sum_equiv (coordinatePerm e).symm
  intro i
  simp [Matrix.reindex_apply,Matrix.submatrix_apply]

theorem population_channel_pure_zero (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    matrixPopulation (channel γ ν (n+1) (pure ψ)) 0 =
      (1-γ)*population ψ 0+γ*ν*vecMass ψ := by
  have hentry (i : Basis n) :
      (channel γ ν (n+1) (pure ψ) (Fin.cons 1 i) (Fin.cons 1 i)).re =
        (γ*ν)*(gram (columns (tensorKraus γ ν n) (branch ψ 0)) i i).re+
          (1-γ*(1-ν))*(gram (columns (tensorKraus γ ν n) (branch ψ 1)) i i).re := by
    rw [channel_first_site_entry]
    rw [local_channel γ ν hγ hν (fun a d ↦
      (columns (tensorKraus γ ν n) (branch ψ a) *
        (columns (tensorKraus γ ν n) (branch ψ d)).conjTranspose) i i)]
    simp [gram]
  have hmass (b : Fin 2) : (∑ i, (gram (columns (tensorKraus γ ν n) (branch ψ b)) i i).re) =
      vecMass (branch ψ b) := by
    simpa only [mass,Matrix.trace,Matrix.diag,Complex.re_sum] using
      mass_channel_columns γ ν hγ hν n (branch ψ b)
  unfold matrixPopulation
  rw [sum_fin_cons]
  simp only [Fin.sum_univ_two,Fin.cons_zero,show (0:Fin 2) ≠ 1 by decide,ite_false,
    Finset.sum_const_zero,zero_add,ite_true,hentry,Finset.sum_add_distrib,← Finset.mul_sum,hmass,
    population_zero,vecMass_branches]
  ring

theorem population_channel_zero (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} {P : QMatrix (n+1)} (hP : IsState P) :
    matrixPopulation (channel γ ν (n+1) P) 0 = (1-γ)*matrixPopulation P 0+γ*ν := by
  let w := hP.1.isHermitian.eigenvalues
  let ψ := fun a i ↦ hP.1.isHermitian.eigenvectorUnitary i a
  have hs : ∑ a, w a = 1 := spectral_weights_sum hP
  have hv (a) : vecMass (ψ a) = 1 := spectral_vectors_mass hP.1.isHermitian a
  have hdecomp : P = ∑ a, w a • pure (ψ a) := spectral_pure_decomposition hP.1.isHermitian
  conv_lhs => rw [hdecomp]
  rw [channel_mixture,matrixPopulation_mixture]
  simp only [population_channel_pure_zero γ ν hγ hν,hv,mul_one]
  conv_rhs => rw [hdecomp]
  rw [matrixPopulation_mixture]
  simp only [matrixPopulation_pure,mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,hs,one_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem channel_population (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} {P : QMatrix n} (hP : IsState P) (j : Fin n) :
    matrixPopulation (channel γ ν n P) j = (1-γ)*matrixPopulation P j+γ*ν := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
      let e : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 j
      let Q := Matrix.reindex (coordinatePerm e) (coordinatePerm e) P
      have hQ : IsState Q := ⟨hP.1.submatrix _, (trace_reindex _ P).trans hP.2⟩
      have h := population_channel_zero γ ν hγ hν hQ
      change matrixPopulation (channel γ ν (n+1) (Matrix.reindex _ _ P)) 0 = _ at h
      rw [← channel_reindex, matrixPopulation_reindex] at h
      change matrixPopulation (channel γ ν (n+1) P) (e.symm 0) =
        (1-γ)*matrixPopulation (Matrix.reindex (coordinatePerm e) (coordinatePerm e) P) 0+γ*ν at h
      rw [matrixPopulation_reindex] at h
      simpa [e] using h

end GAD

end

end OAI
