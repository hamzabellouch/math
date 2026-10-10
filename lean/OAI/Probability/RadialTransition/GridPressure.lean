import OAI.Probability.RadialTransition.MixtureBounds

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

def macroMeasure (m q : ℕ) (z : ℝ) : Measure (MacroState m q) :=
  Measure.pi (fun i : GridIndex m => particleBase (regionMeasure (macroRegion q (gridEmbed i))) z)

def macroProduct (φ : Potential) (m q : ℕ) (β : ℝ) (F : ℕ → ℝ) (x : MacroState m q) : ℝ :=
  ∏ i : GridIndex m, (F (particleCount (x i))*
    Real.exp (-β*pairWithin (fun (y z : macroRegion q (gridEmbed i)) => radialPair φ y z) (x i)))

lemma macroProduct_nonneg (φ : Potential) (m q : ℕ) (β : ℝ) (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n) (x : MacroState m q) : 0 ≤ macroProduct φ m q β F x :=
  Finset.prod_nonneg (fun _ _ => mul_nonneg (hF _) (Real.exp_pos _).le)

lemma integrable_macroProduct {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {q : ℕ} (hq : 0 < q) (m : ℕ) (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hs : Summable (fun n => F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)) :
    Integrable (macroProduct φ m q β F) (macroMeasure m q z) := by
  let (i : GridIndex m) : IsFiniteMeasure (regionMeasure (macroRegion q (gridEmbed i))) :=
    regionMeasure_finite (measurableSet_macroRegion _ _) (by rw [volume_macroRegion hq]; finiteness)
  exact Integrable.fintype_prod_dep (fun i => integrable_macroWeight hφ hb hq (gridEmbed i) β z F hF hs)

lemma integral_macroProduct {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {q : ℕ} (hq : 0 < q) (m : ℕ) (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hs : Summable (fun n => F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)) :
    (∫ x, macroProduct φ m q β F x ∂macroMeasure m q z) =
      (∑' n, F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)^(m^3) := by
  let (i : GridIndex m) : IsFiniteMeasure (regionMeasure (macroRegion q (gridEmbed i))) :=
    regionMeasure_finite (measurableSet_macroRegion _ _) (by rw [volume_macroRegion hq]; finiteness)
  unfold macroProduct macroMeasure
  rw [integral_fintype_prod_eq_prod (fun i : GridIndex m => fun s : ParticleState (macroRegion q (gridEmbed i)) => F (particleCount s)*Real.exp (-β*pairWithin (fun (y w : macroRegion q (gridEmbed i)) => radialPair φ y w) s))]
  simp only [integral_macroWeight hφ hb hq _ β z F hF hs, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin]

lemma macroQuad_upper {φ : Potential} {m q : ℕ} (hq : 0 < q) {β R lam : ℝ}
    (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam) (x : MacroState m q) :
    Real.exp (-β*macroKacEnergy φ m q R lam x) ≤
      macroProduct φ m q β (fun n => Real.exp (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(n:ℝ)^2)) x := by
  have hh := mul_le_mul_of_nonpos_left (macroKacEnergy_lower (φ := φ) hq hR hlam x) (neg_nonpos.mpr hβ)
  apply (Real.exp_le_exp.mpr hh).trans_eq
  simp only [macroProduct, ← Real.exp_add, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma integrable_macroKac {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hq : 0 < q) {β R lam z : ℝ} (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam)
    (hs : Summable (quadraticTerm φ ((q:ℝ)/4) β z (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/2))) :
    Integrable (fun x => Real.exp (-β*macroKacEnergy φ m q R lam x)) (macroMeasure m q z) := by
  have hs' : Summable (fun n : ℕ => Real.exp (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(n:ℝ)^2)*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β) := by
    convert hs using 1
    funext n
    dsimp only [quadraticTerm]
    have he : β*lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(n:ℝ)^2 = β*lam*(1+10000*(bumpLip:ℝ)*q/R)/2*(n:ℝ)^2/((q:ℝ)/4)^3 := by ring
    rw [he]; ring
  apply (integrable_macroProduct hφ hb hq m β z _ (fun _ => (Real.exp_pos _).le) hs').mono'
    (Real.measurable_exp.comp (measurable_const.mul (measurable_macroKacEnergy hφ m q R lam))).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by change |Real.exp (-β*macroKacEnergy φ m q R lam x)| ≤ _; rw [abs_of_pos (Real.exp_pos _)]; exact macroQuad_upper hq hβ hR hlam x)

lemma macroKac_partition_upper {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hq : 0 < q) {β R lam z : ℝ} (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam)
    (hs : Summable (quadraticTerm φ ((q:ℝ)/4) β z (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/2))) :
    boltzmannPartition (macroMeasure m q z) (fun x => β*macroKacEnergy φ m q R lam x) ≤
      (∑' n, quadraticTerm φ ((q:ℝ)/4) β z (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/2) n)^(m^3) := by
  have he (n : ℕ) : Real.exp (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(n:ℝ)^2)*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β =
      quadraticTerm φ ((q:ℝ)/4) β z (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/2) n := by
    dsimp only [quadraticTerm]
    have h : β*lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(n:ℝ)^2 = β*lam*(1+10000*(bumpLip:ℝ)*q/R)/2*(n:ℝ)^2/((q:ℝ)/4)^3 := by ring
    rw [h]; ring
  have hs' : Summable (fun n : ℕ => Real.exp (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(n:ℝ)^2)*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β) := by simpa only [he] using hs
  have hh := integral_mono (integrable_macroKac hφ hb hq hβ hR hlam hs)
    (integrable_macroProduct hφ hb hq m β z _ (fun _ => (Real.exp_pos _).le) hs')
    (macroQuad_upper hq hβ hR hlam)
  rw [integral_macroProduct hφ hb hq m β z _ (fun _ => (Real.exp_pos _).le) hs'] at hh
  simpa only [he, boltzmannPartition, neg_mul] using hh

end RadialTransition

end

end OAI
