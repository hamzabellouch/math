import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.NeumannReindex
import OAI.Analysis.CoulombIonization.FieldAnalysis.PauliMomentum

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NeumannFermions_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

open CoulombAtom
variable {N : ℕ}

def neumannLowerEnergy (N : ℕ) : ℝ :=
  tfKinetic*(N:ℝ)^(5/3:ℝ)-neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))

lemma neumann_coeff_energy_lower
    {Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)} (hΨ : CubeAntisymmetric Ψ)
    (s : Fin N → Fin 2) (n : (Fin N × Fin 3) → ℕ) :
    neumannLowerEnergy N * ‖neumannCoeff (Ψ s) n‖^2 ≤
      ((1/2:ℝ)*∑ i : Fin N × Fin 3, (Real.pi*(n i:ℝ))^2)*‖neumannCoeff (Ψ s) n‖^2 := by
  by_cases h : neumannCoeff (Ψ s) n = 0
  · simp [h]
  · exact mul_le_mul_of_nonneg_right
      (neumann_mode_list_lower n s (coeff_nonzero_injective hΨ s n h)) (sq_nonneg _)

theorem neumann_spin_component_lower
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hanti : CubeAntisymmetric (fun s => finiteCubeFunction (hf s)))
    (s : Fin N → Fin 2) :
    neumannLowerEnergy N * (∫ x, ‖finiteCubeFunction (hf s) x‖^2) ≤
      (1/2:ℝ)*∑ i, ∫ x, ‖finiteCubeGradient (hf s) i x‖^2 := by
  have hm : HasSum
      (fun n => neumannLowerEnergy N*‖neumannCoeff (finiteCubeFunction (hf s)) n‖^2)
      (neumannLowerEnergy N*(∫ x, ‖finiteCubeFunction (hf s) x‖^2)) := by
    rw [←neumann_parseval]
    exact (neumannCoeff_summable (finiteCubeFunction (hf s))).hasSum.mul_left _
  apply hasSum_le_of_sum_le hm
  intro S
  calc
    _ ≤ ∑ n ∈ S, ((1/2:ℝ)*∑ i : Fin N × Fin 3, (Real.pi*(n i:ℝ))^2)*
        ‖neumannCoeff (finiteCubeFunction (hf s)) n‖^2 := by
      exact Finset.sum_le_sum fun n _ => neumann_coeff_energy_lower hanti s n
    _ = (1/2:ℝ)*(∑ n ∈ S, (∑ i : Fin N × Fin 3, (Real.pi*(n i:ℝ))^2)*
        ‖neumannCoeff (finiteCubeFunction (hf s)) n‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_neumann_spectral_lower (hf s) S) (by norm_num)

theorem neumann_fermion_cube_lower
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hanti : CubeAntisymmetric (fun s => finiteCubeFunction (hf s))) :
    neumannLowerEnergy N * (∑ s, ∫ x, ‖finiteCubeFunction (hf s) x‖^2) ≤
      (1/2:ℝ)*∑ s, ∑ i, ∫ x, ‖finiteCubeGradient (hf s) i x‖^2 := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  simpa only [Finset.mul_sum] using neumann_spin_component_lower hf hanti s

end Work_NeumannFermions_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

open CoulombAtom

lemma neumann_mode_family_lower {α : Type*} [Fintype α]
    (n : α → Fin 3 → ℕ) (s : α → Fin 2)
    (h : Function.Injective (fun i => (n i,s i))) :
    neumannLowerEnergy (Fintype.card α) ≤
      (1/2:ℝ)*∑ i, ∑ a, (Real.pi*(n i a:ℝ))^2 := by
  classical
  let e : α ↪ NeumannSpinMode := ⟨_,h⟩
  have hb := neumann_lattice_lower (Finset.univ.map e)
  simp only [Finset.card_map,Finset.card_univ,Finset.sum_map] at hb
  refine hb.trans_eq ?_
  simp only [mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  change (Real.pi^2/2)*(n i a:ℝ)^2 = (1/2:ℝ)*(Real.pi^2*(n i a:ℝ)^2)
  ring

variable {N : ℕ}

lemma coeff_zero_of_exchange
    {Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)}
    (s : Fin N → Fin 2) (n : (Fin N × Fin 3) → ℕ)
    {i j : Fin N}
    (hΨ : ∀ s x, Ψ (s ∘ Equiv.swap i j) (x ∘ particlePermute (Equiv.swap i j)) = -Ψ s x)
    (hs : s i = s j) (hn : ∀ a : Fin 3, n (i,a) = n (j,a)) :
    neumannCoeff (Ψ s) n = 0 := by
  classical
  let e := Equiv.swap i j
  have hse : s ∘ e = s := by
    funext k
    by_cases hki : k=i
    · subst k; simpa [e] using hs.symm
    · by_cases hkj : k=j
      · subst k; simpa [e] using hs
      · simp [e,Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hne : n ∘ (particlePermute e).symm = n := by
    ext ⟨k,a⟩
    by_cases hki : k=i
    · subst k; simpa [e,particlePermute] using (hn a).symm
    · by_cases hkj : k=j
      · subst k; simpa [e,particlePermute] using hn a
      · simp [e,particlePermute,Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hex (x : (Fin N × Fin 3) → I) : Ψ s (x ∘ particlePermute e) = -Ψ s x := by
    have ht := hΨ s x
    change Ψ (s ∘ e) (x ∘ particlePermute e) = -Ψ s x at ht
    rwa [hse] at ht
  have hh := integral_cube_permute (particlePermute e)
    (fun x => conj (cubeNeumannMode n x)*Ψ s x)
  simp only [cubeNeumannMode_permute,hne,hex,mul_neg,integral_neg] at hh
  change -neumannCoeff (Ψ s) n = neumannCoeff (Ψ s) n at hh
  exact neg_eq_self.mp hh

variable {C : Type*} [DecidableEq C]

def CellAntisymmetric (c : Fin N → C)
    (Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)) : Prop :=
  ∀ i j, i ≠ j → c i=c j → ∀ s x,
    Ψ (s ∘ Equiv.swap i j) (x ∘ particlePermute (Equiv.swap i j)) = -Ψ s x

def cellCount (c : Fin N → C) (a : C) : ℕ := (Finset.univ.filter (fun i => c i=a)).card

def cellLowerEnergy (c : Fin N → C) : ℝ :=
  ∑ a ∈ Finset.univ.image c, neumannLowerEnergy (cellCount c a)

lemma cellCount_eq_fintype (c : Fin N → C) (a : C) :
    cellCount c a = Fintype.card {i : Fin N // c i=a} := by
  simp [cellCount,Fintype.card_subtype]

omit [DecidableEq C] in
lemma cell_coeff_injective (c : Fin N → C)
    {Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)} (hΨ : CellAntisymmetric c Ψ)
    (s : Fin N → Fin 2) (n : (Fin N × Fin 3) → ℕ)
    (hc : neumannCoeff (Ψ s) n ≠ 0) (a : C) :
    Function.Injective (fun i : {i : Fin N // c i=a} => ((fun k : Fin 3 => n (i.1,k)),s i.1)) := by
  intro i j h
  apply Subtype.ext
  by_contra hij
  apply hc
  exact coeff_zero_of_exchange s n (hΨ i.1 j.1 hij (i.2.trans j.2.symm))
    (congrArg Prod.snd h) (fun k => congrFun (congrArg Prod.fst h) k)

lemma cell_coeff_energy_lower (c : Fin N → C)
    {Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)} (hΨ : CellAntisymmetric c Ψ)
    (s : Fin N → Fin 2) (n : (Fin N × Fin 3) → ℕ) :
    cellLowerEnergy c*‖neumannCoeff (Ψ s) n‖^2 ≤
      ((1/2:ℝ)*∑ i : Fin N × Fin 3, (Real.pi*(n i:ℝ))^2)*‖neumannCoeff (Ψ s) n‖^2 := by
  classical
  by_cases hz : neumannCoeff (Ψ s) n = 0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    calc
      _ ≤ ∑ a ∈ Finset.univ.image c,
          (1/2:ℝ)*∑ i ∈ Finset.univ.filter (fun i => c i=a), ∑ k : Fin 3, (Real.pi*(n (i,k):ℝ))^2 := by
        apply Finset.sum_le_sum
        intro a _
        rw [cellCount_eq_fintype]
        have hh := neumann_mode_family_lower
          (fun i : {i : Fin N // c i=a} => fun k => n (i.1,k))
          (fun i : {i : Fin N // c i=a} => s i.1) (cell_coeff_injective c hΨ s n hz a)
        rw [Finset.sum_subtype (p := fun i => c i=a) (Finset.univ.filter (fun i => c i=a))
          (by intro i; simp) (fun i => ∑ k : Fin 3, (Real.pi*(n (i,k):ℝ))^2)]
        exact hh
      _ = _ := by
        rw [←Finset.mul_sum,Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem c (Finset.mem_univ i)),Fintype.sum_prod_type]

theorem neumann_cell_component_lower (c : Fin N → C)
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hanti : CellAntisymmetric c (fun s => finiteCubeFunction (hf s)))
    (s : Fin N → Fin 2) :
    cellLowerEnergy c * (∫ x, ‖finiteCubeFunction (hf s) x‖^2) ≤
      (1/2:ℝ)*∑ i, ∫ x, ‖finiteCubeGradient (hf s) i x‖^2 := by
  have hm : HasSum
      (fun n => cellLowerEnergy c*‖neumannCoeff (finiteCubeFunction (hf s)) n‖^2)
      (cellLowerEnergy c*(∫ x, ‖finiteCubeFunction (hf s) x‖^2)) := by
    rw [←neumann_parseval]
    exact (neumannCoeff_summable (finiteCubeFunction (hf s))).hasSum.mul_left _
  apply hasSum_le_of_sum_le hm
  intro S
  calc
    _ ≤ ∑ n ∈ S, ((1/2:ℝ)*∑ i : Fin N × Fin 3, (Real.pi*(n i:ℝ))^2)*
        ‖neumannCoeff (finiteCubeFunction (hf s)) n‖^2 := by
      exact Finset.sum_le_sum fun n _ => cell_coeff_energy_lower c hanti s n
    _ = (1/2:ℝ)*(∑ n ∈ S, (∑ i : Fin N × Fin 3, (Real.pi*(n i:ℝ))^2)*
        ‖neumannCoeff (finiteCubeFunction (hf s)) n‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_neumann_spectral_lower (hf s) S) (by norm_num)

end CoulombNeumann

end

end OAI
