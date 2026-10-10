import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationErrorPhysical
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedErrorRaw
import OAI.Analysis.LipschitzHilbert.Phase.SourceLabeledAngularErrorData
import OAI.Analysis.LipschitzHilbert.Estimates.SlopeTopNeighborhood

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item) (horder : 6 ≤ P.order)
  (t a c Cwide M Lip radius : ℝ) (E J K H : ℕ)
  (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1)
  (hC : Cwide ≤ c*(2:ℝ)^J) (hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
  (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (hradius : radius ≤ K)
  (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
    (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k))
  (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
  (hsupport : ∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
  (hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
    ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
  (hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| → b j l k s = 0)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem selector_error_top_neighborhood_of_supported
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (T : SlopeBox) (Kw : ℝ) (D : ℕ) (hKw : 0 < Kw)
    (G : SourceSupportedLabeledTopGeometry P T Kw D) (ht : T.slope = t)
    (hdecay : 6+2*(8*D+1) ≤ P.order) (B : ℝ) (hB : 0 ≤ B)
    (i : Fin 2) (rate L : ℝ) :
    let Err := P.angularErrorFamily horder t a c Cwide M Lip radius E J K H
      ha hc hc1 hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1
    (∀ y, (Err.sources y).sourceBound ≤ B) →
    (∀ y, (Err.sources y).sumBound ≤ B) →
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*T.area) ∧
      ∀ lower upper z shift, |shift| ≤ Kw*T.width → z ∉ bad →
        ‖(P.withProfile alt hAlt).rawInterval (P.physicalAngularErrorCoefficient t a b v g)
          (i.castLE (by decide)) lower upper z.1 (z.2-t*z.1+shift)‖ ≤
          (256^(8*D+1)*(16*topPairConstant P.absoluteConstant (8*D+1)*
            selectorErrorMomentBase B)*(topExceptionMoment (topAreaPrefactor Kw) rate L:ℝ)*
              5^(8*D))*(T.weight Kw (D:ℝ) z)^8 := by
  dsimp only
  intro hsource hsum
  let Err := P.angularErrorFamily horder t a c Cwide M Lip radius E J K H
    ha hc hc1 hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1
  let Q := P.withProfile alt hAlt
  let raw := fun (e : Fin 2) j (p : Σ l : P.labels j, Item j l) k y =>
    Q.raw (⟨i.val+e.val,by omega⟩ : Fin 3) j p.1 p.2 k y
  let F := fun ab : ℕ×ℕ => fun x y => Q.rawInterval
    (P.physicalAngularErrorCoefficient t a b v g) (i.castLE (by decide)) ab.1 ab.2 x y
  have hcoeff (j : Fin N) (p : Σ l : P.labels j, Item j l) :
      Err.coefficient j p.1 p.2 = P.physicalAngularErrorCoefficient t a b v g j p.1 p.2 :=
    P.angularErrorFamily_coefficient horder t a c Cwide M Lip radius E J K H
      ha hc hc1 hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1 _ _ _
  have hraw0 j p k y x : raw 0 j p k y x = Q.raw (i.castLE (by decide)) j p.1 p.2 k y x := by
    congr 2
  obtain ⟨bad,hbad,harea,hpoint⟩ := slope_top_neighborhood T Kw
    (256^(8*D+1)*(16*topPairConstant P.absoluteConstant (8*D+1)*selectorErrorMomentBase B))
    rate L D hKw (by
      have := topPairConstant_pos P.absoluteConstant (8*D+1) P.absoluteConstant_pos
      have := selectorErrorMomentBase_pos hB
      positivity) F (by
        intro n hn
        obtain ⟨bad,hbad,harea,hpoint⟩ := Err.error_synthesis_global_neighborhood_of_supported B
          P.absoluteConstant T.x (T.y-T.slope*T.x) (Kw*T.length) (Kw*T.width)
          hB P.absoluteConstant_pos (mul_pos hKw T.length_pos) (mul_pos hKw T.width_pos)
          hsource hsum G.length_le G.width_le
          (by
            intro j l u
            simp only [Err,angularErrorFamily,zero_add]
            change |P.length j*(P.snappedSite j l u).1-T.x| ≤ Kw*T.length
            exact P.snapped_supported_top_horizontal G j l u)
          (by
            intro j l u
            simp only [Err,angularErrorFamily,zero_add]
            exact P.snapped_supported_top_vertical G j l u)
          raw P.frequency (8*D+1) n (by omega) hn
          (by
            intro e j l u k y x
            simp only [Err,angularErrorFamily,zero_add]
            change ‖Q.raw ⟨i.val+e.val,by omega⟩ j l u k y x‖ ≤ Q.absoluteConstant*
              (lineEnvelope (Q.length j*(Q.snappedSite j l u).1) (Q.length j)
                (6+2*(8*D+1)) x *
               lineEnvelope (Q.width*(Q.snappedSite j l u).2) Q.width (6+2*(8*D+1)) y)
            exact Q.raw_absolute_snapped_decay (6+2*(8*D+1)) hdecay
              ⟨i.val+e.val,by omega⟩ j l u k y x)
          (by
            intro j p k x y
            have hs : (4:ℂ)*(↑(Kw*T.width):ℂ) = (P.scale:ℂ) := by
              rw [G.scale_eq]
              push_cast
              ring
            rw [hs]
            fin_cases i
            · exact modulatedPlanarJet_covariant_zero (alt j p.1 p.2 k)
                (P.actualX j p.1 p.2) (P.actualZ j p.1 p.2) (P.length j) P.width
                (-P.rowSlope j p.1) (P.frequency k) P.scale y (P.length_pos j).ne' x
            · exact modulatedPlanarJet_covariant_one (alt j p.1 p.2 k)
                (P.actualX j p.1 p.2) (P.actualZ j p.1 p.2) (P.length j) P.width
                (-P.rowSlope j p.1) (P.frequency k) P.scale y (P.length_pos j).ne' x)
          (by
            intro e j p k
            exact modulatedPlanarJet_continuous (alt j p.1 p.2 k)
              (P.actualX j p.1 p.2) (P.actualZ j p.1 p.2) (P.length j) P.width
              (-P.rowSlope j p.1) (P.frequency k) P.scale (P.length_pos j).ne' _)
          (by
            intro j p k x y
            exact modulatedPlanarJet_differentiable (alt j p.1 p.2 k)
              (P.actualX j p.1 p.2) (P.actualZ j p.1 p.2) (P.length j) P.width
              (-P.rowSlope j p.1) (P.frequency k) P.scale y (P.length_pos j).ne' _ x)
        refine ⟨bad,hbad,harea,?_⟩
        intro ab x z shift hshift hout
        have h := hpoint ab.1 ab.2 x z shift hshift hout
        simp only [hcoeff,hraw0] at h
        simpa only [F,rawInterval,Nat.add_sub_cancel,mul_assoc] using h)
  refine ⟨bad,hbad,harea,?_⟩
  intro lower upper z shift hshift hout
  simpa only [F,ht] using hpoint (lower,upper) z shift hshift hout

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
