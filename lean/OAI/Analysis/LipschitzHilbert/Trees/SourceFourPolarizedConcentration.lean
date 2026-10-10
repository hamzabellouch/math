import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeConcentration
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticePolarizationSpectrum

namespace OAI

/-! One exceptional set works for all four self-packet families used
in polarization. Their common raw constant doubles, which costs one
power of L; the fixed fourfold area cost is absorbed by two additional
units in the exponential decay rate. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LipschitzHilbert

def packetPolarizationPhase (i : Fin 4) : ℂ :=
  if i = 0 then 1 else if i = 1 then -1 else if i = 2 then Complex.I else -Complex.I

theorem packetPolarizationPhase_norm (i : Fin 4) : ‖packetPolarizationPhase i‖ = 1 := by
  fin_cases i <;> simp [packetPolarizationPhase]

private theorem four_exp_decay {J L : ℝ} (hL : 2 ≤ L) :
    4 * Real.exp (-(J + 2) * L) ≤ Real.exp (-J * L) := by
  have he : 4 ≤ Real.exp (2 * L) := by
    have h := Real.add_one_le_exp (2 * L)
    linarith
  have hd : 4 / Real.exp (2 * L) ≤ 1 := (div_le_one (Real.exp_pos _)).mpr he
  have hi : -(J + 2) * L = -J * L + -(2 * L) := by ring
  rw [hi, Real.exp_add, Real.exp_neg]
  calc
    _ = Real.exp (-J * L) * (4 / Real.exp (2 * L)) := by ring
    _ ≤ Real.exp (-J * L) * 1 := mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
    _ = _ := mul_one _

namespace SourceLatticePacket

private theorem polarize_topGeometry {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
    (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
    (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)
    (c : ℂ) (hc : ‖c‖ = 1) (T : SlopeBox) (K : ℝ) (D : ℕ)
    (G : SourceLatticeTopGeometry P T K D) :
    SourceLatticeTopGeometry (P.polarize alt hAlt c hc) T K D where
  length_le := G.length_le
  width_le := G.width_le
  centerX_le := G.centerX_le
  centerZ_le := G.centerZ_le
  order_le := G.order_le
  scale_eq := G.scale_eq

theorem source_four_polarized_concentration (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hcStar : 0 ≤ cStar) (hCEta : 0 ≤ CEta)
    (hgap : cStar < cEta * cb) (J a p : ℝ) (D : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ i, Fin (N i) → Type) [∀ i j, Fintype (ι i j)]
        (P : ∀ i, SourceLatticePacket (N i) κ (ι i)), (∀ i, (P i).constant ≤ L ^ p) →
      ∀ (alt : ∀ i j, ι i j → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ i j u k,
          planarProfileConstant (alt i j u k) (2 * (P i).order) ≤ (P i).profileBound)
        (cutoff : ∀ i, Fin (N i) → ℝ) (v : τ → ℝ × ℝ → ℝ),
      (∀ i, Measurable (v i)) →
      ∀ (g : τ → ℝ × ℝ → EuclideanSpace ℂ κ), (∀ i, Measurable (g i)) →
      (∀ i z, ‖g i z‖ ≤ 1) → (∀ i, Monotone (cutoff i)) →
      ∀ (T : τ → SlopeBox) (w : ℝ), 0 < w →
      (∀ i j u k ξ η, planarAngularFourier ((P i).physicalPacket (T i).slope j u k) (ξ, η) ≠ 0 →
        |ξ + ((T i).slope + (P i).rowSlope j) * η| ≤ cStar / (P i).length j ∧
          cEta ≤ w * η ∧ w * η ≤ CEta) →
      (∀ i j u k ξ η,
        planarAngularFourier (((P i).withProfile (alt i) (hAlt i)).physicalPacket
          (T i).slope j u k) (ξ, η) ≠ 0 →
        |ξ + ((T i).slope + (P i).rowSlope j) * η| ≤ cStar / (P i).length j ∧
          cEta ≤ w * η ∧ w * η ≤ CEta) →
      (∀ i j (_u : ι i j), cb * w / (P i).length j ≤ |(P i).rowSlope j| ∧
        |(P i).rowSlope j| ≤ Cb * w / (P i).length j) →
      (∀ i, SourceLatticeTopGeometry (P i) (T i) (L ^ a) D) →
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J * L) * (∑ i, (T i).area)) ∧
        ∀ i (phase : Fin 4) lower upper, lower ≤ upper → upper ≤ N i → ∀ z shift,
          |shift| ≤ (T i).width → z ∉ bad →
          let Q := (P i).polarize (alt i) (hAlt i)
            (packetPolarizationPhase phase) (packetPolarizationPhase_norm phase)
          let F := fun x y => planarPacketInterval
            (Q.family.mainCoefficient (cutoff i) (v i) (g i))
            (fun j u k t s => Q.raw 0 j u k t s) lower upper x y
          ‖F z.1 ((z.2 - (T i).slope * z.1) + shift)‖ +
            (T i).width * ‖covariantSignal Q.frequency (fun k t => F z.1 t k)
              ((z.2 - (T i).slope * z.1) + shift)‖ ≤
                L ^ (2 * p + 5) * ((T i).weight (L ^ a) (D : ℝ) z) ^ 8 := by
  classical
  obtain ⟨L0, hL0, hgood⟩ := source_lattice_concentration hL
    cStar cEta CEta cb Cb hcEta hcb hCb hcStar hCEta hgap (J + 2) a (p + 1) D
    (by linarith) ha (by linarith)
  refine ⟨L0, hL0, ?_⟩
  intro L hLL τ κ _ _ N ι _ P hP alt hAlt cutoff v hv g hg hg1 hcut T w hw hspectrum haltSpectrum hselector G
  have hL2 : 2 ≤ L := hL0.trans hLL
  have hLp : 0 < L := by linarith
  let Q : ∀ q : τ × Fin 4, SourceLatticePacket (N q.1) κ (ι q.1) := fun q =>
    (P q.1).polarize (alt q.1) (hAlt q.1)
      (packetPolarizationPhase q.2) (packetPolarizationPhase_norm q.2)
  have hQ (q : τ × Fin 4) : (Q q).constant ≤ L ^ (p + 1) := by
    rw [show (Q q).constant = 2 * (P q.1).constant from
      (P q.1).polarize_constant (alt q.1) (hAlt q.1) _ _]
    calc
      2 * (P q.1).constant ≤ 2 * L ^ p := mul_le_mul_of_nonneg_left (hP q.1) (by norm_num)
      _ ≤ L * L ^ p := mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hLp.le _)
      _ = L ^ (p + 1) := by rw [Real.rpow_add hLp, Real.rpow_one]; ring
  have hspec (q : τ × Fin 4) := (P q.1).polarize_spectrum (alt q.1) (hAlt q.1)
    (packetPolarizationPhase q.2) (packetPolarizationPhase_norm q.2)
    (T q.1).slope w cStar cEta CEta (hspectrum q.1) (haltSpectrum q.1)
  obtain ⟨bad, hbad, harea, hpoint⟩ := hgood L hLL (τ × Fin 4) κ
    (fun q => N q.1) (fun q => ι q.1) Q hQ (fun q => cutoff q.1)
    (fun q => v q.1) (fun q => hv q.1) (fun q => g q.1) (fun q => hg q.1)
    (fun q => hg1 q.1) (fun q => hcut q.1) (fun q => T q.1) w hw hspec
    (fun q => hselector q.1) (fun q => polarize_topGeometry (P q.1) (alt q.1)
      (hAlt q.1) _ _ (T q.1) (L ^ a) D (G q.1))
  refine ⟨bad, hbad, ?_, ?_⟩
  · apply harea.trans
    apply ENNReal.ofReal_le_ofReal
    have hsum : (∑ q : τ × Fin 4, (T q.1).area) = 4 * ∑ i, (T i).area := by
      simp [Fintype.sum_prod_type, ← Finset.mul_sum]
    rw [hsum]
    calc
      Real.exp (-(J + 2) * L) * (4 * ∑ i, (T i).area) =
          (4 * Real.exp (-(J + 2) * L)) * ∑ i, (T i).area := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (four_exp_decay hL2)
        (Finset.sum_nonneg (fun i _ => (T i).area_pos.le))
  · intro i phase lower upper hlu hu z shift hshift hout
    have h := hpoint (i, phase) lower upper hlu hu z shift hshift hout
    have hexponent : 2 * (p + 1) + 3 = 2 * p + 5 := by ring
    simpa only [hexponent] using h

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
