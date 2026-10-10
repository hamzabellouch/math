import OAI.Analysis.CircleDomains.Topology.InitialCollarPrescribedLimits
import OAI.Analysis.CircleDomains.Topology.FinalCollarPrescribedLimits
import OAI.Analysis.CircleDomains.Selection.FivePieceSplicing

namespace OAI

/-! Assemble the two actual collar tails and a selected actual middle
fragment using the common limiting budget. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def HasShortCollarJoining (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (C T : Set X) : Prop :=
  ∀z ∈ C, ∀ε : ℝ≥0∞, 0 < ε → ∃U : Set X, U ∈ 𝓝 z ∧
    ∀a ∈ U ∩ C, ∀b ∈ U ∩ C, ∃ρ : TaggedPhysicalPath d,
      AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧ ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧
        range ρ.1.val ⊆ T ∧ physicalTollCost d g m ρ.1 ≤ ε

theorem exists_twoEnded_collar_splicing_of_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : X) (V W : ℕ → Set X) (hV : ∀j, IsOpen (V j)) (hW : ∀j, IsOpen (W j))
    (hnestV : ∀j, closure (V (j+1)) ⊆ V j) (hnestW : ∀j, closure (W (j+1)) ⊆ W j)
    (hshrinkV : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (V j) ⊆ O)
    (hshrinkW : ∀O ∈ 𝓝 q, ∃k : ℕ, ∀j ≥ k, closure (W j) ⊆ O)
    (hstartV : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hendV : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    (hstartW : ∀n, (Γ n).1.val ⊥ ∉ W 0) (hendW : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    (hmid : ∀n, firstExitTime (Γ n).1.val (V 0) < lastEntryTime (Γ n).1.val (W 0))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hmV : ∀j z, z ∈ frontier (V j) → m z = 0)
    (hmW : ∀j z, z ∈ frontier (W j) → m z = 0)
    (x y : ℕ → X) (c e : ℕ → ℝ≥0∞) (M A : ℝ≥0∞) (hA : A < ∞)
    (hx : ∀j, Tendsto (fun n => (Γ n).1.val (firstExitTime (Γ n).1.val (V j))) atTop (𝓝 (x j)))
    (hy : ∀j, Tendsto (fun n => (Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) atTop (𝓝 (y j)))
    (hc : ∀hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) < firstExitTime (Γ n).1.val (V j),
      ∀j, Tendsto (fun n => physicalTollCost d g m (firstExitFragmentArray d hU Γ V hcut n j).1) atTop (𝓝 (c j)))
    (he : ∀hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)),
      ∀j, Tendsto (fun n => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut n j).1) atTop (𝓝 (e j)))
    (hM : Tendsto (fun n => physicalTollCost d g m (restrictTaggedPhysicalPath d hU (Γ n) (hmid n)).1) atTop (𝓝 M))
    (hbudget : M + (∑'j, c j) + (∑'j, e j) ≤ A)
    (hsmallV : ∀j, HasShortCollarJoining d ν N g m (frontier (V (j+1))) (closure (V j)))
    (hsmallW : ∀j, HasShortCollarJoining d ν N g m (frontier (W (j+1))) (closure (W j)))
    (houterV : HasShortCollarJoining d ν N g m (frontier (V 0)) univ)
    (houterW : HasShortCollarJoining d ν N g m (frontier (W 0)) univ)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η := by
  have haV : Antitone V := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnestV j))
  have haW : Antitone W := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnestW j))
  have hfrontV (n : ℕ) : (Γ n).1.val (firstExitTime (Γ n).1.val (V 0)) ∈ frontier (V 0) :=
    firstExit_frontier (Γ n).1.val (hV 0) (haV (Nat.zero_le _) (hstartV n)) (hendV n)
  have hfrontW (n : ℕ) : (Γ n).1.val (lastEntryTime (Γ n).1.val (W 0)) ∈ frontier (W 0) :=
    lastEntry_frontier (Γ n).1.val (hW 0) (hstartW n) (haW (Nat.zero_le _) (hendW n))
  have hx0 : x 0 ∈ frontier (V 0) :=
    isClosed_frontier.mem_of_tendsto (hx 0) (Eventually.of_forall hfrontV)
  have hy0 : y 0 ∈ frontier (W 0) :=
    isClosed_frontier.mem_of_tendsto (hy 0) (Eventually.of_forall hfrontW)
  have hfinite := hbudget.trans_lt hA
  have hMfin : M < ∞ := (ENNReal.add_lt_top.mp (ENNReal.add_lt_top.mp hfinite).1).1
  have hCfin : (∑'j, c j) < ∞ := (ENNReal.add_lt_top.mp (ENNReal.add_lt_top.mp hfinite).1).2
  have hEfin : (∑'j, e j) < ∞ := (ENNReal.add_lt_top.mp hfinite).2
  let ε : ℝ≥0∞ := ENNReal.ofReal (η/5)
  have hδ : 0 < η/5 := by positivity
  have hε : 0 < ε := ENNReal.ofReal_pos.mpr hδ
  obtain ⟨O, hO, hjoinV⟩ := houterV (x 0) hx0 ε hε
  obtain ⟨P, hP, hjoinW⟩ := houterW (y 0) hy0 ε hε
  obtain ⟨i, α, θα, hα, hα0, hα1, hαO, hαcost⟩ := exists_initial_collar_path_of_limits
    d hU hG ν N Γ hΓ p V hV hnestV hshrinkV hstartV hendV g hg m hmV
    (∑'j, c j) hCfin x c hx hc le_rfl O hO hsmallV w hw hpos hpoint hδ
  obtain ⟨j, β, θβ, hβ, hβ0, hβ1, hβP, hβcost⟩ := exists_final_collar_path_of_limits
    d hU hG ν N Γ hΓ q W hW hnestW hshrinkW hstartW hendW g hg m hmW
    (∑'j, e j) hEfin y e hy he le_rfl P hP hsmallW w hw hpos hpoint hδ
  have hMc : ∀ᶠn in atTop, physicalTollCost d g m (restrictTaggedPhysicalPath d hU (Γ n) (hmid n)).1 < M + ε :=
    (tendsto_order.mp hM).2 _ (ENNReal.lt_add_right hMfin.ne hε.ne')
  obtain ⟨k, hkO, hkP, hkcost⟩ :=
    (((hx 0).eventually hO).and (((hy 0).eventually hP).and hMc)).exists
  let μ := restrictTaggedPhysicalPath d hU (Γ k) (hmid k)
  have hμ : AllowedTaggedPath d ν N (μ.1.val, μ.2) :=
    restrictTaggedPhysicalPath_allowed d hU ν N (Γ k) (hΓ k) hpoint (hmid k)
  have hμ0 : μ.1.val ⊥ = (Γ k).1.val (firstExitTime (Γ k).1.val (V 0)) :=
    restrictTaggedPhysicalPath_zero d hU (Γ k) (hmid k)
  have hμ1 : μ.1.val ⊤ = (Γ k).1.val (lastEntryTime (Γ k).1.val (W 0)) :=
    restrictTaggedPhysicalPath_one d hU (Γ k) (hmid k)
  obtain ⟨a, ha, ha0, ha1, _, hacost⟩ := hjoinV (α.val ⊤)
    ⟨hαO, hα1.symm ▸ hfrontV i⟩ (μ.1.val ⊥) ⟨hμ0.symm ▸ hkO, hμ0.symm ▸ hfrontV k⟩
  obtain ⟨b, hb, hb0, hb1, _, hbcost⟩ := hjoinW (μ.1.val ⊤)
    ⟨hμ1.symm ▸ hkP, hμ1.symm ▸ hfrontW k⟩ (β.val ⊤) ⟨hβP, hβ1.symm ▸ hfrontW j⟩
  obtain ⟨βr, θr, hβr, hβr0, hβr1, hβrcost⟩ :=
    exists_allowed_reversed_interior_cost d ν N (β, θβ) hβ g m hpoint
  have hαm : m (α.val ⊤) = 0 := by rw [hα1]; exact hmV 0 _ (hfrontV i)
  have hμm0 : m (μ.1.val ⊥) = 0 := by rw [hμ0]; exact hmV 0 _ (hfrontV k)
  have hμm1 : m (μ.1.val ⊤) = 0 := by rw [hμ1]; exact hmW 0 _ (hfrontW k)
  have hβm : m (β.val ⊤) = 0 := by rw [hβ1]; exact hmW 0 _ (hfrontW j)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hρcost⟩ := exists_allowed_five_piece_splicing d hU ν N
    (α, θα) a μ b (βr, θr) hα ha hμ hb hβr ha0.symm ha1 hb0.symm
    (hb1.trans hβr0.symm) g hg m hαm (by rw [ha1]; exact hμm0) hμm1
    (by rw [hb1]; exact hβm) hpoint
  refine ⟨ρ, θ, hρ, hρ0.trans hα0, hρ1.trans (hβr1.trans hβ0), ?_⟩
  have hεsum : ε + ε + ε + ε + ε = ENNReal.ofReal η := by
    dsimp [ε]
    rw [← ENNReal.ofReal_add hδ.le hδ.le,
      ← ENNReal.ofReal_add (by positivity) hδ.le,
      ← ENNReal.ofReal_add (by positivity) hδ.le,
      ← ENNReal.ofReal_add (by positivity) hδ.le]
    congr 1
    ring
  calc
    interiorPhysicalTollCost d g m ρ = _ := hρcost
    _ ≤ (((∑'j, c j) + ε) + ε + (M + ε) + ε + ((∑'j, e j) + ε)) := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · exact add_le_add hαcost ((interiorPhysicalTollCost_le_full d g m a.1).trans hacost)
          · exact (interiorPhysicalTollCost_le_full d g m μ.1).trans hkcost.le
        · exact (interiorPhysicalTollCost_le_full d g m b.1).trans hbcost
      · rw [hβrcost]
        exact hβcost
    _ = (M + (∑'j, c j) + (∑'j, e j)) + (ε + ε + ε + ε + ε) := by ac_rfl
    _ ≤ A + ENNReal.ofReal η := by rw [hεsum]; exact add_le_add hbudget le_rfl

end CircleDomainRigidity

end

end OAI
