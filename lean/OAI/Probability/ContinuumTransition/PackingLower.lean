import OAI.Probability.ContinuumTransition.TetraVolume

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

lemma core_one_term (t β d r : ℝ) (c : Space) :
    familyTerm (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d)
      (Metric.closedBall c r) 1 = volume.real (Metric.closedBall (0 : Space) r)*Real.exp d := by
  have he (x : Fin 1 → Space) :
      gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d (Fin 1) x = Real.exp d := by
    have hi : Function.Injective x := fun i j _ => Subsingleton.elim _ _
    simp [gibbsFamily, hi, gibbsEnergy]
  simp only [familyTerm, familyIntegral, he, setIntegral_const, smul_eq_mul,
    Measure.real, volume_generalConfigurations, Fintype.card_fin, pow_one]
  simp [Measure.addHaar_closedBall_center]

theorem core_grand_packing_lower {t β η r B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hη : 0 ≤ η) (hr : 2*r ≤ η) (hB : 0 ≤ B) (d L : ℝ) (n : ℕ)
    (hterm : ∀ c : Space, B ≤ familyTerm
      (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) (Metric.closedBall c r) n) :
    B^(packingNumber L) ≤ grandIntegral
      (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) (cube ((1+η)*L+2*r)) := by
  obtain ⟨x,hx,hs⟩ := packingNumber_realized L
  obtain ⟨hc,hsep⟩ := dilate_packing hη x hx hs
  let A : Fin (packingNumber L) → Set Space := fun i => Metric.closedBall ((1+η) • x i) r
  let U : Space → Space → ℝ := fun x y => coreProfile t ‖x-y‖
  let F := gibbsFamily U β d
  let s : Finset (Fin (packingNumber L)) := Finset.univ
  have hAU : (⋃ i ∈ s, A i) ⊆ cube ((1+η)*L+2*r) := by
    apply iUnion₂_subset
    intro i _
    exact closedBall_subset_cube (hc i)
  have hfin : GrandFinite F (cube ((1+η)*L+2*r)) :=
    core_gibbs_finite t d hβ (isCompact_cube _).measure_lt_top.ne
  have hfinU := hfin.mono_set hAU (gibbsFamily_nonneg U β d)
  have hm : Measurable (Function.uncurry U) :=
    (measurable_coreProfile t).comp ((measurable_fst.sub measurable_snd).norm)
  have hA (i : Fin (packingNumber L)) (_ : i ∈ s) : MeasurableSet (A i) := measurableSet_closedBall
  have hFU := hfinU.fixedOccupation (fun _ => n) hA
    (fun ι _ => measurable_gibbsFamily hm β d ι) (gibbsFamily_nonneg U β d)
  have he := grandIntegral_fixedOccupation_product hm
    (fun a b => congrArg (coreProfile t) (norm_sub_rev a b)) β d A (fun _ => n) s hA
    (fun _ _ _ _ hij => packingBalls_disjoint hη hr hsep hij)
    (fun _ _ _ _ hij _ ha _ hb => coreProfile_eq_zero ht
      (closedBall_cross_sep hη hr (hsep _ _ hij) ha hb)) hfinU
  calc
    B^(packingNumber L) = ∏ _i ∈ s, B := by simp [s]
    _ ≤ ∏ i ∈ s, familyTerm F (A i) n :=
      Finset.prod_le_prod₀ (fun _ _ => hB) (fun i _ => hterm ((1+η) • x i))
    _ = grandIntegral (fixedOccupationFamily A s (fun _ => n) F) (⋃ i ∈ s, A i) := he.symm
    _ ≤ grandIntegral F (⋃ i ∈ s, A i) := by
      apply grandIntegral_mono _ _ (MeasurableSet.biUnion s.finite_toSet.countable hA)
        (fun _ => hFU.integrable _) (fun _ => hfinU.integrable _) hFU.summable hfinU.summable
      intro n x _
      unfold fixedOccupationFamily
      split_ifs
      · rfl
      · exact gibbsFamily_nonneg U β d (Fin n) x
    _ ≤ _ := grandIntegral_mono_set F hAU (gibbsFamily_nonneg U β d)
      (fun _ => hfin.integrable _) hfinU.summable hfin.summable

end ContinuumTemperature
end

end OAI
