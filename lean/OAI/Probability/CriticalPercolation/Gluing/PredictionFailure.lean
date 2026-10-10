import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.FreshTrial

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma prediction_persists (q : E → unitInterval) (S T U σ τ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet[blockSigma U] A)
    (hST : S∩U=T∩U) (hstates : ∀ e∈S∩U, (e∈σ ↔ e∈τ)) :
    blockProbability q S A σ=blockProbability q T A τ := by
  unfold blockProbability
  congr 1
  ext ω
  have hrestrict : U∩forceOn S σ ω=U∩forceOn T τ ω := by
    ext e
    by_cases he : e∈U
    · have heST : e∈S ↔ e∈T := by
        have hh := Set.ext_iff.mp hST e
        simpa only [Set.mem_inter_iff,he,and_true] using hh
      by_cases heS : e∈S
      · have heT := heST.mp heS
        simp only [Set.mem_inter_iff,he,true_and,mem_forceOn,ite_eq_left heS,ite_eq_left heT]
        exact hstates e ⟨heS,he⟩
      · have heT : e∉T := fun h => heS (heST.mpr h)
        simp only [Set.mem_inter_iff,he,true_and,mem_forceOn,ite_eq_right heS,ite_eq_right heT]
    · simp only [Set.mem_inter_iff,he,false_and]
  have hforce : forceOn U (forceOn S σ ω) (forceOn T τ ω)=forceOn T τ ω := by
    ext e
    by_cases he : e∈U
    · have hh := Set.ext_iff.mp hrestrict e
      simpa only [Set.mem_inter_iff,he,true_and,mem_forceOn,ite_true,ite_eq_left he] using hh
    · simp only [mem_forceOn,ite_eq_right he]
  have hh := block_event_forceOn U A hA (forceOn S σ ω) (forceOn T τ ω)
  rw [hforce] at hh
  exact hh.symm

lemma blockProbability_real_compl (q : E → unitInterval) (S σ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (blockProbability q S Aᶜ σ).toReal=1-(blockProbability q S A σ).toReal := by
  change (law q).real ((forceOn S σ ⁻¹' A)ᶜ)=1-(law q).real (forceOn S σ ⁻¹' A)
  exact probReal_compl_eq_one_sub (hA.preimage (measurable_forceOn S σ))

lemma integral_known_prediction_defect (q : E → unitInterval) (S : Set E)
    (A C : Set (Set E)) (hA : MeasurableSet[blockSigma S] A) (hC : MeasurableSet C) :
    (∫ σ, A.indicator (fun σ => 1-(blockProbability q S C σ).toReal) σ ∂law q)=
      (law q).real (A\C) := by
  have he : (fun σ => A.indicator (fun σ => 1-(blockProbability q S C σ).toReal) σ)=
      (fun σ => (blockProbability q S (Cᶜ∩A) σ).toReal) := by
    funext σ
    rw [blockProbability_inter_block q S Cᶜ A hA]
    by_cases hσ : σ∈A
    · simp only [Set.indicator_of_mem hσ,blockProbability_real_compl q S σ C hC]
    · simp only [Set.indicator_of_notMem hσ,ENNReal.toReal_zero]
  rw [he,integral_blockProbability_real q S (Cᶜ∩A) (hC.compl.inter ((blockSigma_le S) _ hA))]
  congr 1
  exact Set.inter_comm _ _

lemma bad_prediction_bound (q : E → unitInterval) (S : Set E)
    (A C : Set (Set E)) (hA : MeasurableSet[blockSigma S] A) (hC : MeasurableSet C)
    (δ : ℝ) (hδ : 0<δ) :
    (law q).real (A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ})≤
      (law q).real (A\C)/δ := by
  let g := fun σ => (blockProbability q S C σ).toReal
  let B := A∩{σ : Set E | g σ<1-δ}
  have hg : Measurable g :=
    ((measurable_blockProbability q S C hC).mono (blockSigma_le S) le_rfl).ennreal_toReal
  have hma := (blockSigma_le S) _ hA
  have hmb : MeasurableSet B := hma.inter (measurableSet_lt hg measurable_const)
  have hgi : Integrable g (law q) := integrable_blockProbability_real q S C hC
  have hdef : Integrable (A.indicator (fun σ => 1-g σ)) (law q) :=
    ((integrable_const 1).sub hgi).indicator hma
  have hl : Integrable (fun σ => δ*B.indicator (1 : Set E → ℝ) σ) (law q) :=
    ((integrable_const 1).indicator hmb).const_mul δ
  have hi := integral_mono hl hdef (fun σ => by
    by_cases hσ : σ∈B
    · rw [Set.indicator_of_mem hσ,Set.indicator_of_mem hσ.1]
      dsimp only [Pi.one_apply]
      have hh := hσ.2
      dsimp only [Set.mem_ofPred_eq] at hh
      linarith
    · rw [Set.indicator_of_notMem hσ,mul_zero]
      by_cases hσA : σ∈A
      · rw [Set.indicator_of_mem hσA]
        exact sub_nonneg.mpr (ENNReal.toReal_mono (by simp) (blockProbability_le_one q S C σ))
      · rw [Set.indicator_of_notMem hσA])
  rw [integral_const_mul,integral_indicator_one hmb] at hi
  have he := integral_known_prediction_defect q S A C hA hC
  change (∫ σ, A.indicator (fun σ => 1-g σ) σ ∂law q)=(law q).real (A\C) at he
  rw [he] at hi
  exact (le_div_iff₀ hδ).mpr (by nlinarith [hi])

theorem two_prediction_failure (q : E → unitInterval) (S : Set E)
    (A C D : Set (Set E)) (hA : MeasurableSet[blockSigma S] A)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (δ a : ℝ) (hδ : 0<δ) (hin : 1-δ≤(law q).real A)
    (hCfail : (law q).real (A\C)≤a) (hDfail : (law q).real (A\D)≤a) :
    (law q).real (Aᶜ ∪
      (A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ}) ∪
      (A∩{σ : Set E | (blockProbability q S D σ).toReal<1-δ}))≤δ+2*a/δ := by
  have hma := (blockSigma_le S) _ hA
  have hcomp : (law q).real Aᶜ≤δ := by rw [probReal_compl_eq_one_sub hma]; linarith
  have hc := (bad_prediction_bound q S A C hA hC δ hδ).trans
    (div_le_div_of_nonneg_right hCfail hδ.le)
  have hd := (bad_prediction_bound q S A D hA hD δ hδ).trans
    (div_le_div_of_nonneg_right hDfail hδ.le)
  have h1 := measureReal_union_le (μ := law q) (s₁ := Aᶜ)
    (s₂ := A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ})
  have h2 := measureReal_union_le (μ := law q)
    (s₁ := Aᶜ∪(A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ}))
    (s₂ := A∩{σ : Set E | (blockProbability q S D σ).toReal<1-δ})
  calc
    _ ≤ _ := h2
    _ ≤ (law q).real Aᶜ+(law q).real
        (A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ})+
        (law q).real (A∩{σ : Set E | (blockProbability q S D σ).toReal<1-δ}) :=
      add_le_add h1 le_rfl
    _ ≤ δ+a/δ+a/δ := add_le_add (add_le_add hcomp hc) hd
    _ = δ+2*a/δ := by ring

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
