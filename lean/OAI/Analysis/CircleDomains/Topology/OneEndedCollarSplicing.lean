import OAI.Analysis.CircleDomains.Topology.TwoEndedCollarSplicing
import OAI.Analysis.CircleDomains.Modulus.ActualOneEndedBudget

namespace OAI

/-! Attach one actual retained prefix to the final collar tail, keeping
its original initial point and using the joint prefix/tail budget. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_oneEnded_collar_splicing_of_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set X) (hF : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : X) (W : ℕ → Set X) (hW : ∀j, IsOpen (W j))
    (hnest : ∀j, closure (W (j+1)) ⊆ W j)
    (hshrink : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (W j) ⊆ O)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0) (hend : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    (hprefix : ∀n, ⊥ < lastEntryTime (Γ n).1.val (W 0))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀j z, z ∈ frontier (W j) → m z = 0) (hzero : ∀n, m ((Γ n).1.val ⊥) = 0)
    (x : ℕ → X) (c : ℕ → ℝ≥0∞) (M A : ℝ≥0∞) (hA : A < ∞)
    (hx : ∀j, Tendsto (fun n => (Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) atTop (𝓝 (x j)))
    (hc : ∀hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)),
      ∀j, Tendsto (fun n => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut n j).1) atTop (𝓝 (c j)))
    (hM : Tendsto (fun n => physicalTollCost d g m (prefixFragment d hU Γ W hprefix n).1) atTop (𝓝 M))
    (hbudget : M + (∑'j, c j) ≤ A)
    (hsmall : ∀j, HasShortCollarJoining d ν N g m (frontier (W (j+1))) (closure (W j)))
    (houter : HasShortCollarJoining d ν N g m (frontier (W 0)) univ)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η := by
  have ha : Antitone W := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hfront (n : ℕ) : (Γ n).1.val (lastEntryTime (Γ n).1.val (W 0)) ∈ frontier (W 0) :=
    lastEntry_frontier (Γ n).1.val (hW 0) (hstart n) (ha (Nat.zero_le _) (hend n))
  have hx0 : x 0 ∈ frontier (W 0) :=
    isClosed_frontier.mem_of_tendsto (hx 0) (Eventually.of_forall hfront)
  have hfinite := hbudget.trans_lt hA
  have hMfin : M < ∞ := (ENNReal.add_lt_top.mp hfinite).1
  have hCfin : (∑'j, c j) < ∞ := (ENNReal.add_lt_top.mp hfinite).2
  let ε : ℝ≥0∞ := ENNReal.ofReal (η/3)
  have hδ : 0 < η/3 := by positivity
  have hε : 0 < ε := ENNReal.ofReal_pos.mpr hδ
  obtain ⟨O, hO, hjoin⟩ := houter (x 0) hx0 ε hε
  obtain ⟨i, β, θβ, hβ, hβ0, hβ1, hβO, hβcost⟩ := exists_final_collar_path_of_limits
    d hU hG ν N Γ hΓ p W hW hnest hshrink hstart hend g hg m hm
    (∑'j, c j) hCfin x c hx hc le_rfl O hO hsmall w hw hpos hpoint hδ
  have hMc : ∀ᶠn in atTop, physicalTollCost d g m (prefixFragment d hU Γ W hprefix n).1 < M + ε :=
    (tendsto_order.mp hM).2 _ (ENNReal.lt_add_right hMfin.ne hε.ne')
  obtain ⟨k, hkO, hkcost⟩ := (((hx 0).eventually hO).and hMc).exists
  let α := prefixFragment d hU Γ W hprefix k
  have hα : AllowedTaggedPath d ν N (α.1.val, α.2) :=
    restrictTaggedPhysicalPath_allowed d hU ν N (Γ k) (hΓ k) hpoint (hprefix k)
  have hα0 : α.1.val ⊥ = (Γ k).1.val ⊥ := restrictTaggedPhysicalPath_zero d hU (Γ k) (hprefix k)
  have hα1 : α.1.val ⊤ = (Γ k).1.val (lastEntryTime (Γ k).1.val (W 0)) :=
    restrictTaggedPhysicalPath_one d hU (Γ k) (hprefix k)
  obtain ⟨a, haA, ha0, ha1, _, hacost⟩ := hjoin (α.1.val ⊤)
    ⟨hα1.symm ▸ hkO, hα1.symm ▸ hfront k⟩ (β.val ⊤) ⟨hβO, hβ1.symm ▸ hfront i⟩
  obtain ⟨βr, θr, hβr, hβr0, hβr1, hβrcost⟩ :=
    exists_allowed_reversed_interior_cost d ν N (β, θβ) hβ g m hpoint
  have hαm : m (α.1.val ⊤) = 0 := by rw [hα1]; exact hm 0 _ (hfront k)
  have ham : m (a.1.val ⊤) = 0 := by rw [ha1, hβ1]; exact hm 0 _ (hfront i)
  obtain ⟨αa, θαa, hαa, hαa0, hαa1, hαacost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N α a hα haA ha0.symm g hg m hαm hpoint
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hρcost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N (αa, θαa) (βr, θr) hαa hβr
      (hαa1.trans (ha1.trans hβr0.symm)) g hg m (by rw [hαa1]; exact ham) hpoint
  have hstartρ : ρ.val ⊥ = (Γ k).1.val ⊥ := hρ0.trans (hαa0.trans hα0)
  refine ⟨ρ, θ, hρ, hstartρ.symm ▸ hF k, hρ1.trans (hβr1.trans hβ0), ?_⟩
  rw [preterminalToll_eq_interior_of_initial_zero ρ.val m (by rw [hstartρ]; exact hzero k)]
  change interiorPhysicalTollCost d g m ρ ≤ _
  have hεsum : ε + ε + ε = ENNReal.ofReal η := by
    dsimp [ε]
    rw [← ENNReal.ofReal_add hδ.le hδ.le, ← ENNReal.ofReal_add (by positivity) hδ.le]
    congr 1
    ring
  calc
    interiorPhysicalTollCost d g m ρ =
        interiorPhysicalTollCost d g m α.1 + interiorPhysicalTollCost d g m a.1 +
          interiorPhysicalTollCost d g m β := by rw [hρcost, hαacost, hβrcost]
    _ ≤ (M + ε) + ε + ((∑'j, c j) + ε) :=
      add_le_add (add_le_add ((interiorPhysicalTollCost_le_full d g m α.1).trans hkcost.le)
        ((interiorPhysicalTollCost_le_full d g m a.1).trans hacost)) hβcost
    _ = (M + (∑'j, c j)) + (ε + ε + ε) := by ac_rfl
    _ ≤ A + ENNReal.ofReal η := by rw [hεsum]; exact add_le_add hbudget le_rfl

end CircleDomainRigidity

end

end OAI
