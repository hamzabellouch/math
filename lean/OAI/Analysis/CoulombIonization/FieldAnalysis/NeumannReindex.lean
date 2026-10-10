import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.NeumannGradient

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NeumannReindex_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

variable {d e : Type*} [Fintype d] [Fintype e]

lemma integral_cube_reindex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : d ≃ e) (f : (e → I) → E) :
    (∫ x : d → I, f (x ∘ a.symm)) = ∫ x, f x := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : e => I) a).integral_comp' f
  change (∫ x, f ((MeasurableEquiv.piCongrLeft (fun _ : e => I) a) x)) = _ at h
  convert h using 1
  congr 1
  funext x
  congr 1
  funext i
  simp only [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_eq_cast,Function.comp_def]
  rfl

lemma cubeNeumannMode_reindex (a : d ≃ e) (n : e → ℕ) (x : d → I) :
    cubeNeumannMode n (x ∘ a.symm) = cubeNeumannMode (n ∘ a) x := by
  simp only [cubeNeumannMode,ContinuousMap.coe_mk,Function.comp_def]
  simpa only [a.symm_apply_apply] using
    (a.prod_comp (fun i => neumannMode (n i) (x (a.symm i)))).symm

def realReindex (a : d ≃ e) : (d → ℝ) ≃L[ℝ] (e → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : e => ℝ) a

omit [Fintype d] [Fintype e] in
lemma realReindex_apply (a : d ≃ e) (x : d → ℝ) : realReindex a x = x ∘ a.symm := by
  funext i
  change (Equiv.piCongrLeft (fun _ : e => ℝ) a) x i = _
  simp only [Equiv.piCongrLeft_apply_eq_cast,Function.comp_def]
  rfl

omit [Fintype d] [Fintype e] in
lemma realReindex_single [DecidableEq d] [DecidableEq e] (a : d ≃ e) (i : d) :
    realReindex a (Pi.single i 1) = Pi.single (a i) 1 := by
  rw [realReindex_apply]
  funext j
  simp only [Function.comp_def,Pi.single_apply]
  simp only [a.symm_apply_eq]

def finiteCubeFunction {f : (d → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) : C(d → I,ℂ) where
  toFun x := f (fun i => (x i:ℝ))
  continuous_toFun := hf.continuous.comp (by fun_prop)

def finiteCubeGradient {f : (d → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (i : d) : C(d → I,ℂ) := by
  classical
  exact {toFun := fun x => fderiv ℝ f (fun j => (x j:ℝ)) (Pi.single i 1)
         continuous_toFun := ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp (by fun_prop)}

lemma finiteCubeFunction_reindex {f : (e → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (a : d ≃ e)
    (x : d → I) :
    finiteCubeFunction (hf.comp (realReindex a).contDiff) x = finiteCubeFunction hf (x ∘ a.symm) := by
  simp only [finiteCubeFunction,ContinuousMap.coe_mk,Function.comp_def,realReindex_apply]

lemma finiteCubeGradient_reindex {f : (e → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (a : d ≃ e)
    (i : d) (x : d → I) :
    finiteCubeGradient (hf.comp (realReindex a).contDiff) i x =
      finiteCubeGradient hf (a i) (x ∘ a.symm) := by
  classical
  simp only [finiteCubeGradient,ContinuousMap.coe_mk]
  rw [fderiv_comp _ (hf.differentiable (by simp) _) ((realReindex a).differentiableAt),
    ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    realReindex_single,realReindex_apply]
  rfl

lemma neumannCoeff_reindex {f : (e → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (a : d ≃ e)
    (n : e → ℕ) :
    neumannCoeff (finiteCubeFunction (hf.comp (realReindex a).contDiff)) (n ∘ a) =
      neumannCoeff (finiteCubeFunction hf) n := by
  unfold neumannCoeff
  calc
    _ = ∫ x : d → I, conj (cubeNeumannMode n (x ∘ a.symm))*finiteCubeFunction hf (x ∘ a.symm) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [finiteCubeFunction_reindex hf a x,cubeNeumannMode_reindex]
    _ = _ := integral_cube_reindex a (fun x => conj (cubeNeumannMode n x)*finiteCubeFunction hf x)

lemma cubeGradient_eq_finite {D : ℕ} {f : (Fin (D+1) → ℝ) → ℂ}
    (hf : ContDiff ℝ 1 f) (i : Fin (D+1)) : cubeGradient hf i = finiteCubeGradient hf i := by
  ext x
  simp only [cubeGradient,finiteCubeGradient,ContinuousMap.coe_mk]
  apply congrArg (fderiv ℝ f (fun j => (x j:ℝ)))
  funext j
  by_cases hj : j=i <;> simp [hj]

theorem finite_neumann_spectral_lower {f : (d → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (S : Finset (d → ℕ)) :
    ∑ n ∈ S, (∑ i, (Real.pi*(n i:ℝ))^2)*‖neumannCoeff (finiteCubeFunction hf) n‖^2 ≤
      ∑ i, ∫ x, ‖finiteCubeGradient hf i x‖^2 := by
  classical
  cases isEmpty_or_nonempty d with
  | inl hd => simp
  | inr hd =>
    let D := Fintype.card d-1
    have hc : Fintype.card (Fin (D+1)) = Fintype.card d := by
      simp only [Fintype.card_fin]
      dsimp [D]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
    let a : Fin (D+1) ≃ d := Fintype.equivOfCardEq hc
    let A : (d → ℕ) ↪ (Fin (D+1) → ℕ) :=
      ⟨fun n => n ∘ a,fun n m h => by funext j; simpa using congrFun h (a.symm j)⟩
    have hh := neumann_spectral_lower (hf.comp (realReindex a).contDiff) (S.map A)
    have hl : (∑ n ∈ S.map A, (∑ i, (Real.pi*(n i:ℝ))^2)*
        ‖neumannCoeff (cubeFunction (hf.comp (realReindex a).contDiff)) n‖^2) =
        ∑ n ∈ S, (∑ i, (Real.pi*(n i:ℝ))^2)*‖neumannCoeff (finiteCubeFunction hf) n‖^2 := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro n _
      change (∑ i, (Real.pi*(n (a i):ℝ))^2)*
        ‖neumannCoeff (finiteCubeFunction (hf.comp (realReindex a).contDiff)) (n ∘ a)‖^2 = _
      rw [neumannCoeff_reindex hf a n]
      rw [a.sum_comp (fun i => (Real.pi*(n i:ℝ))^2)]
    have hr : (∑ i, ∫ x, ‖cubeGradient (hf.comp (realReindex a).contDiff) i x‖^2) =
        ∑ i, ∫ x, ‖finiteCubeGradient hf i x‖^2 := by
      calc
        _ = ∑ i : Fin (D+1), ∫ x, ‖finiteCubeGradient hf (a i) x‖^2 := by
          apply Finset.sum_congr rfl
          intro i _
          simp_rw [cubeGradient_eq_finite,finiteCubeGradient_reindex hf a i]
          exact integral_cube_reindex a (fun x => ‖finiteCubeGradient hf (a i) x‖^2)
        _ = _ := a.sum_comp (fun i => ∫ x, ‖finiteCubeGradient hf i x‖^2)
    rwa [hl,hr] at hh

end Work_NeumannReindex_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

variable {d : Type*} [Fintype d]

lemma integral_cube_permute (e : d ≃ d) (f : (d → I) → ℂ) :
    (∫ x, f (x ∘ e)) = ∫ x, f x := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : d => I) e.symm).integral_comp' f
  change (∫ x, f ((MeasurableEquiv.piCongrLeft (fun _ : d => I) e.symm) x)) = _ at h
  convert h using 1
  congr 1
  funext x
  congr 1
  funext i
  simp only [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_eq_cast,Equiv.symm_symm,
    Function.comp_def]
  rfl

lemma cubeNeumannMode_permute (e : d ≃ d) (n : d → ℕ) (x : d → I) :
    cubeNeumannMode n (x ∘ e) = cubeNeumannMode (n ∘ e.symm) x := by
  simp only [cubeNeumannMode,ContinuousMap.coe_mk,Function.comp_def]
  simpa only [e.symm_apply_apply] using
    e.prod_comp (fun i => neumannMode (n (e.symm i)) (x i))

variable {N : ℕ}

abbrev particlePermute (e : Equiv.Perm (Fin N)) : Equiv.Perm (Fin N × Fin 3) :=
  e.prodCongr (Equiv.refl (Fin 3))

def CubeAntisymmetric (Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)) : Prop :=
  ∀ i j, i ≠ j → ∀ s x,
    Ψ (s ∘ Equiv.swap i j) (x ∘ particlePermute (Equiv.swap i j)) = -Ψ s x

lemma coeff_zero_of_repeated_mode
    {Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)} (hΨ : CubeAntisymmetric Ψ)
    (s : Fin N → Fin 2) (n : (Fin N × Fin 3) → ℕ)
    {i j : Fin N} (hij : i ≠ j) (hs : s i = s j)
    (hn : ∀ a : Fin 3, n (i,a) = n (j,a)) :
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
    have ht := hΨ i j hij s x
    change Ψ (s ∘ e) (x ∘ particlePermute e) = -Ψ s x at ht
    rwa [hse] at ht
  have hh := integral_cube_permute (particlePermute e)
    (fun x => conj (cubeNeumannMode n x)*Ψ s x)
  simp only [cubeNeumannMode_permute,hne,hex,mul_neg,integral_neg] at hh
  change -neumannCoeff (Ψ s) n = neumannCoeff (Ψ s) n at hh
  exact neg_eq_self.mp hh

theorem coeff_nonzero_injective
    {Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)} (hΨ : CubeAntisymmetric Ψ)
    (s : Fin N → Fin 2) (n : (Fin N × Fin 3) → ℕ)
    (hc : neumannCoeff (Ψ s) n ≠ 0) :
    Function.Injective (fun i => ((fun a : Fin 3 => n (i,a)),s i)) := by
  intro i j h
  by_contra hij
  apply hc
  exact coeff_zero_of_repeated_mode hΨ s n hij (congrArg Prod.snd h)
    (fun a => congrFun (congrArg Prod.fst h) a)

end CoulombNeumann

end

end OAI
