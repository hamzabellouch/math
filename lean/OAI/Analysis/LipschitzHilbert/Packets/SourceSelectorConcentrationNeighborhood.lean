import OAI.Analysis.LipschitzHilbert.Estimates.ConstructedSynthesisNeighborhood
import OAI.Analysis.LipschitzHilbert.Packets.TopRawPacketData
import OAI.Analysis.LipschitzHilbert.Estimates.SlopeTopNeighborhood

namespace OAI

/-! Weighted top concentration with the original analyzing packets and
an independently chosen synthesis jet pair. This is the source bridge
needed when a selector is frozen only in the analyzing coefficient. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.PlanarPacketFamily

theorem constructed_analyzed_top_neighborhood (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (cutoff : Fin N → ℝ) (v : ℝ×ℝ → ℝ), Measurable v →
      ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      Monotone cutoff →
      (∀ y j u k x, ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x*
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ j u k y xi, |xi| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k y) xi = 0) →
      (∀ j u k y xi, hi*(2:ℝ)^j.val < |xi| → 𝓕 (P.wave j u k y) xi = 0) →
      ∀ (raw : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
        (frequency : κ → ℝ) (T : SlopeBox) (K : ℝ) (D : ℕ), 0 < K →
      P.topLength ≤ K*T.length → P.width ≤ K*T.width →
      (∀ j u, |P.centerX j u-T.x| ≤ K*T.length) →
      (∀ j u, |P.centerZ j u-(T.y-T.slope*T.x)| ≤ K*T.width) →
      (∀ i y j u k x, ‖raw i j u k y x‖ ≤ P.constant*
        (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x*
          lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)) →
      (∀ i y j u k x, ‖deriv (raw i j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x*
          lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)) →
      (∀ i y j u k xi, |xi| < lo*(2:ℝ)^j.val → 𝓕 (raw i j u k y) xi = 0) →
      (∀ i y j u k xi, hi*(2:ℝ)^j.val < |xi| → 𝓕 (raw i j u k y) xi = 0) →
      (∀ y j u k x, (4*(K*T.width):ℂ)*
        (deriv (fun yy => raw 0 j u k yy x) y-
          (frequency k:ℂ)*Complex.I*raw 0 j u k y x) = raw 1 j u k y x) →
      (∀ i j u k, Continuous (fun z : ℝ×ℝ => raw i j u k z.1 z.2)) →
      (∀ j u k x y, DifferentiableAt ℝ (fun yy => raw 0 j u k yy x) y) →
      ∀ J L : ℝ,
      let n := topExceptionMoment (topAreaPrefactor K) J L
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ z w, |w| ≤ K*T.width → z ∉ bad →
          ‖planarPacketInterval (P.mainCoefficient cutoff v g)
            (fun j u k y x => raw 0 j u k y x) a b z.1 ((z.2-T.slope*z.1)+w)‖ ≤
              (P.topPacketAmplitude Ab Am D*(n:ℝ)*5^(8*D))*(T.weight K (D:ℝ) z)^8 := by
  obtain ⟨Ab,Am,hAb,hAm,hglobal⟩ := constructed_synthesis_global_neighborhood hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P cutoff v hv g hg hg1 hd hPderiv hPlow hPhigh raw frequency
    T K D hK hlength hwidth hcenterX hcenterZ hbound hderiv hlow hhigh hcov hcont hdiff J L
  let I := {ab : ℕ×ℕ // ab.1 ≤ ab.2 ∧ ab.2 ≤ N}
  let F : I → ℝ → ℝ → EuclideanSpace ℂ κ := fun ab x y =>
    planarPacketInterval (P.mainCoefficient cutoff v g)
      (fun j u k yy xx => raw 0 j u k yy xx) ab.val.1 ab.val.2 x y
  obtain ⟨bad,hbad,harea,hpoint⟩ := slope_top_neighborhood T K
    (P.topPacketAmplitude Ab Am D) J L D hK (P.topPacketAmplitude_pos Ab Am D).le F (by
      intro n hn
      obtain ⟨bad,hbad,harea,hpoint⟩ := hglobal N κ ι P cutoff v hv g hg hg1 hd
        hPderiv hPlow hPhigh raw frequency T.x (T.y-T.slope*T.x)
        (K*T.length) (K*T.width) (8*D+1)
        (mul_pos hK T.length_pos) (mul_pos hK T.width_pos) (by omega)
        hlength hwidth hcenterX hcenterZ hbound hderiv hlow hhigh
        (fun y j u k x => by simpa only [Complex.ofReal_mul] using hcov y j u k x)
        hcont hdiff n hn
      refine ⟨bad,hbad,harea,?_⟩
      intro ab x y w hw hout
      have hp := hpoint ab.val.1 ab.val.2 ab.property.1 ab.property.2 x y w hw hout
      simp only [Nat.add_sub_cancel] at hp
      convert hp using 1
      dsimp [F,topPacketAmplitude]
      ring)
  refine ⟨bad,hbad,harea,?_⟩
  intro a b hab hb z w hw hout
  exact hpoint (⟨(a,b),hab,hb⟩ : I) z w hw hout

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
