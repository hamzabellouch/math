import OAI.NumberTheory.Jacobsthal.Estimates.SingletonSubsetMass
import OAI.NumberTheory.Jacobsthal.Paths.WrongOwnerBoxMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SubsetPrimeBoxMass
open _root_.Filter FiniteWeightedChoiceBox SingletonSubsetMass PrimeBinAlignmentMass
open WrongOwnerSearchTail WrongOwnerBinMass ActualBinOwners ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem no_nearfull_subset_mass {n : ℕ} (R : Fin n → ℝ) (xi eta : ℝ) (mult : Fin n → ℕ)
    (hR : ∀ i,0 < R i) (hxi : 0 ≤ xi) (heta : 0 ≤ eta) (S : Finset (Fin n))
    (hsingle : ∀ i ∈ S,mult i=1) (a : ℕ → ℤ) (q : ℚ)
    (hd : ∀ i ∈ S,(((primeBin (R i) xi).filter (aligns a q)).card:ℝ) ≤
      (1-eta)*((primeBin (R i) xi).card:ℝ)) :
    (∑ f ∈ restrictedPoints (fun i => (primeBin (R i) xi).powersetCard (mult i)) S
      (fun _ s => ∀ p ∈ s,aligns a q p),pointWeight (fun _ => subsetWeight) f) ≤
      (1-eta/(1+xi))^S.card*boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i))
        (fun _ => subsetWeight) := by
  apply restriction_mass_bound
  · intro i s
    exact subsetWeight_nonnegative s
  · intro i hi
    rw [hsingle i hi,singleton_total_mass]
    have he := singleton_all_mass (primeBin (R i) xi) (aligns a q)
    calc
      _ = mass ((primeBin (R i) xi).filter (aligns a q)) := by
        convert! he using 1
        exact Finset.sum_congr (by ext s; simp only [Finset.mem_filter]) (fun _ _ => rfl)
      _ ≤ _ := non_nearfull_mass (hR i) hxi heta _ (Finset.filter_subset _ _) (hd i hi)

theorem no_nearfull_subset_power {n : ℕ} (R : Fin n → ℝ) (w c xi eta : ℝ) (mult : Fin n → ℕ)
    (hR : ∀ i,0 < R i) (hw : 1 < w) (hc : 0 < c) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (S : Finset (Fin n))
    (hsingle : ∀ i ∈ S,mult i=1) (hcount : c*Real.log w ≤ (S.card:ℝ)) (a : ℕ → ℤ) (q : ℚ)
    (hd : ∀ i ∈ S,(((primeBin (R i) xi).filter (aligns a q)).card:ℝ) ≤
      (1-eta)*((primeBin (R i) xi).card:ℝ)) :
    (∑ f ∈ restrictedPoints (fun i => (primeBin (R i) xi).powersetCard (mult i)) S
      (fun _ s => ∀ p ∈ s,aligns a q p),pointWeight (fun _ => subsetWeight) f) ≤
      w^(-(c*eta/2))*boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i))
        (fun _ => subsetWeight) := by
  have hmass : 0 ≤ boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i)) (fun _ => subsetWeight) := by
    exact Finset.sum_nonneg (fun f _ => weight_nonnegative _ (fun _ => subsetWeight_nonnegative) f)
  exact (no_nearfull_subset_mass R xi eta mult hR hxi0 heta0.le S hsingle a q hd).trans
    (mul_le_mul_of_nonneg_right (PrimeChoiceAlignmentDecay.search_power_bound hw hc heta0 heta1 hxi0 hxi1 S.card hcount) hmass)

theorem wrong_owner_subset_mass {Cs theta A : ℝ} (hCs : 0 ≤ Cs) (htheta : 0 < theta) (hA : 0 < A) :
    ∀ᶠ w : ℝ in atTop,∀ Y xi eta : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) → theta ≤ xi → xi ≤ 1 →
      ∀ (n : ℕ) (R : Fin n → ℝ) (mult : Fin n → ℕ) (S : Finset (Fin n)),
      (∀ i ∈ S,mult i=1) → (∀ i ∈ S,w^(w^((1/4:ℝ))) ≤ R i) →
      ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      (∑ f ∈ (points (fun i => (primeBin (R i) xi).powersetCard (mult i))).filter
        (fun f => ∃ i ∈ S,∃ p ∈ f i,p ∈ wrongOwnerPrimes Y w Cs eta (R i) xi a q),
        pointWeight (fun _ => subsetWeight) f) ≤
      (S.card:ℝ)*w^(-A)*boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i))
        (fun _ => subsetWeight) := by
  filter_upwards [actual_wrong_search_mass hCs htheta hA] with w hw
  intro Y xi eta hY hYup hxi hxi1 n R mult S hsingle hsearch a q hq
  have hh := union_mass_bound (fun i => (primeBin (R i) xi).powersetCard (mult i))
    (fun _ => subsetWeight) (fun _ s => subsetWeight_nonnegative s) S
    (fun i s => ∃ p ∈ s,p ∈ wrongOwnerPrimes Y w Cs eta (R i) xi a q) (w^(-A)) (by
      intro i hi
      rw [hsingle i hi,singleton_total_mass]
      have he := singleton_some_mass (primeBin (R i) xi) (wrongOwnerPrimes Y w Cs eta (R i) xi a q)
        (Finset.filter_subset _ _)
      calc
        _ = mass (wrongOwnerPrimes Y w Cs eta (R i) xi a q) := by
          convert! he using 1
          exact Finset.sum_congr (by ext s; simp only [Finset.mem_filter]) (fun _ _ => rfl)
        _ ≤ _ := hw Y (R i) xi eta hY hYup (hsearch i hi) hxi hxi1 a q hq)
  convert! hh using 1
  exact Finset.sum_congr (by ext f; simp only [Finset.mem_filter]) (fun _ _ => rfl)
end NumberTheoryLean.SubsetPrimeBoxMass


end Erdos970

end OAI
