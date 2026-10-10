import OAI.MeasureTheory.Falconer.Recursion.SuffixDirectionGeometry
import OAI.MeasureTheory.Falconer.Angular.SuffixAngularRadius
import OAI.MeasureTheory.Falconer.Recursion.DescriptorGoodTransfer

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_suffix_good_transport {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      ∀ p : ℕ, d.a ≤ p → p ≤ d.t → d.t ≤ d.N →
      ∀ P C : CellPath, P.length = p → C.length = p →
      P.take d.a = d.X → C.take d.a = d.Y →
      ∀ x ∈ (d.Q.descendant P).carrier, ∀ y ∈ (d.Q.descendant C).carrier,
      (x,y) ∈ d.good → ∀ x' ∈ (d.Q.descendant P).carrier,
      ∀ y' ∈ (d.Q.descendant C).carrier,
      (x',y') ∈ ({d with t := p, i := d.i+1} : PositiveDistanceData).good := by
  obtain ⟨N₀,hN₀⟩ := uniform_descriptor_good_transfer hsig hJ
  refine ⟨N₀,?_⟩
  intro d hsig' hJ' hN hQ hs hq p hap hpt htN P C hP hC hPX hCY x hx y hy hg x' hx' y' hy'
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have hmove := d.fine_directions hQ hs hP hC hPX hCY hx hy hx' hy'
  intro b hb
  have hb' := policyDescriptorList_mono (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) le_rfl hpt hb
  have hbg := hg b hb'
  have hanchor : descriptorAnchor b ≤ p :=
    policyDescriptor_anchor_le_end _ hq hb
  have hl := policyDescriptor_twice_length (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) hq hb
  dsimp only at hl
  have hrad : dist (sourceRadialUnit y x) (sourceRadialUnit y' x') ≤
      sourceAngularRadius d.N sig (descriptorLength b) :=
    hmove.trans (dyadic_ratio_le_radius hsig.le (by omega))
  have hvalid := policyDescriptor_valid (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) hq
    (hpt.trans htN) hb
  have htransfer (A : CellPath) (hA : A.length = descriptorAnchor b)
      (hAω : sourceRadialUnit y x ∈ descriptorGoodSet d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i A b) :
      sourceRadialUnit y' x' ∈ descriptorGoodSet d.Q d.ρ d.mass d.N d.lam d.sig d.J (d.i+1) A b := by
    rw [hsig',hJ'] at hAω ⊢
    exact hN₀ d.N hN d.Q hQ d.ρ d.mass d.lam d.i b hvalid A hA _ _ hrad hAω
  constructor
  · intro A hA hxA
    have hlen := (mem_dyadicPaths _ _).mp hA
    apply htransfer A hlen
    apply hbg.1 A hA
    exact d.Q.same_ancestor hside hlen (by omega) hxA hx' hx
  · intro A hA hyA
    have hlen := (mem_dyadicPaths _ _).mp hA
    apply htransfer A hlen
    apply hbg.2 A hA
    exact d.Q.same_ancestor hside hlen (by omega) hyA hy' hy

end PlanarFalconer

end OAI
