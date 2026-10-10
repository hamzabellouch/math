import OAI.Analysis.LipschitzHilbert.Packets.TopRawPacketData
import OAI.Analysis.LipschitzHilbert.Estimates.SlopeTopNeighborhood

namespace OAI

/-! The actual integral-defined top packet sum, on the physical plane,
has a common exceptional set for all intervals and vertical shifts. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PlanarPacketFamily

theorem constructed_top_neighborhood (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      Monotone cutoff → ∀ (T : SlopeBox) (K : ℝ) (D : ℕ), 0 < K →
      TopRawPacketData P lo hi T K D → ∀ J L : ℝ,
      let n := topExceptionMoment (topAreaPrefactor K) J L
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ z w, |w| ≤ K*T.width → z ∉ bad →
          ‖planarPacketInterval (P.mainCoefficient cutoff v g)
            (fun j u k y x => P.wave j u k y x) a b z.1 ((z.2-T.slope*z.1)+w)‖ ≤
              (P.topPacketAmplitude Ab Am D*(n:ℝ)*5^(8*D))*(T.weight K (D:ℝ) z)^8 := by
  obtain ⟨Ab,Am,hAb,hAm,hglobal⟩ := constructed_global_neighborhood hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P cutoff v hv g hg hg1 hd T K D hK data J L
  let I := {ab : ℕ × ℕ // ab.1 ≤ ab.2 ∧ ab.2 ≤ N}
  let F : I → ℝ → ℝ → EuclideanSpace ℂ κ := fun ab x y =>
    planarPacketInterval (P.mainCoefficient cutoff v g)
      (fun j u k t s => P.wave j u k t s) ab.val.1 ab.val.2 x y
  obtain ⟨bad,hbad,harea,hpoint⟩ := slope_top_neighborhood T K
    (P.topPacketAmplitude Ab Am D) J L D hK (P.topPacketAmplitude_pos Ab Am D).le F (by
      intro n hn
      obtain ⟨bad,hbad,harea,hpoint⟩ := hglobal N κ ι P cutoff v hv g hg hg1 hd
        data.raw data.frequency T.x (T.y-T.slope*T.x) (K*T.length) (K*T.width) (8*D+1)
        (mul_pos hK T.length_pos) (mul_pos hK T.width_pos) (by omega)
        data.length_le data.width_le data.centerX_le data.centerZ_le data.wave_eq
        data.bound data.derivative_bound data.low data.high
        (fun y j u k x => by simpa only [Complex.ofReal_mul] using data.covariant y j u k x)
        data.continuous data.differentiable n hn
      refine ⟨bad,hbad,harea,?_⟩
      intro ab x y w hw hout
      have hp := hpoint ab.val.1 ab.val.2 ab.property.1 ab.property.2 x y w hw hout
      simp only [Nat.add_sub_cancel] at hp
      convert hp using 1
      dsimp [F, topPacketAmplitude]
      ring)
  refine ⟨bad,hbad,harea,?_⟩
  intro a b hab hb z w hw hout
  exact hpoint (⟨(a,b),hab,hb⟩ : I) z w hw hout

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
