import OAI.Analysis.LipschitzHilbert.Trees.SourceTopConcentration
import OAI.Analysis.LipschitzHilbert.Trees.SourceCovariantTop

namespace OAI

/-! The joint top-sum and covariant-derivative bound of §5, including a
common physical-plane exception and a threshold fixed before the family. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PlanarPacketFamily

theorem source_top_good (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (J a p : ℝ) (D : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ i, Fin (N i) → Type) [∀ i j, Fintype (ι i j)]
        (P : ∀ i, PlanarPacketFamily (N i) κ (ι i)), (∀ i, (P i).constant ≤ L^p) →
      ∀ (cutoff : ∀ i, Fin (N i) → ℝ) (v : τ → ℝ × ℝ → ℝ), (∀ i, Measurable (v i)) →
      ∀ (g : τ → ℝ × ℝ → EuclideanSpace ℂ κ), (∀ i, Measurable (g i)) →
      (∀ i z, ‖g i z‖ ≤ 1) → (∀ i, Monotone (cutoff i)) →
      ∀ (T : τ → SlopeBox) (data : ∀ i, TopRawPacketData (P i) lo hi (T i) (L^a) D),
      (∀ i, TopCovariantData (data i)) →
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ i, (T i).area)) ∧
        ∀ i lower upper, lower ≤ upper → upper ≤ N i → ∀ z w,
          |w| ≤ (T i).width → z ∉ bad →
          let F := fun x y => planarPacketInterval ((P i).mainCoefficient (cutoff i) (v i) (g i))
            (fun j u k t s => (P i).wave j u k t s) lower upper x y
          ‖F z.1 ((z.2-(T i).slope*z.1)+w)‖ +
            (T i).width*‖covariantSignal (data i).frequency (fun k t => F z.1 t k)
              ((z.2-(T i).slope*z.1)+w)‖ ≤
                L^(2*p+3)*((T i).weight (L^a) (D:ℝ) z)^8 := by
  obtain ⟨Lf,hLf,hf⟩ := source_top_concentration hL hlo hhi (J+1) a p D (by linarith) ha hp
  obtain ⟨Ld,hLd,hd⟩ := source_covariant_top hL hlo hhi (J+1) a p D (by linarith) ha hp
  refine ⟨max 2 (max Lf Ld),le_max_left _ _,?_⟩
  intro L hL τ κ _ _ N ι _ P hP cutoff v hv g hg hg1 hc T data second
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hLfL : Lf ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLdL : Ld ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨badF,hbadF,hareaF,hpointF⟩ := hf L hLfL τ κ N ι P hP cutoff v hv g hg hg1 hc T data
  obtain ⟨badD,hbadD,hareaD,hpointD⟩ := hd L hLdL τ κ N ι P hP cutoff v hv g hg hg1 hc T data second
  have hS : 0 ≤ ∑ i, (T i).area := Finset.sum_nonneg (fun i _ => (T i).area_pos.le)
  have hexp : 2*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
    have htwo : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    calc
      _ ≤ Real.exp L*Real.exp (-(J+1)*L) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-J*L) := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨badF ∪ badD,hbadF.union hbadD,?_,?_⟩
  · calc
      _ ≤ (volume.prod volume) badF+(volume.prod volume) badD := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(J+1)*L)*(∑ i, (T i).area))+
          ENNReal.ofReal (Real.exp (-(J+1)*L)*(∑ i, (T i).area)) := add_le_add hareaF hareaD
      _ = ENNReal.ofReal ((2*Real.exp (-(J+1)*L))*(∑ i, (T i).area)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hexp
        (Finset.sum_nonneg fun i _ => (T i).area_pos.le))
  · intro i lower upper hlu hu z w hw hout
    dsimp only
    have hK : 1 ≤ L^a := Real.one_le_rpow hL1 ha
    have hW := (T i).width_pos
    have hwidth : (T i).width ≤ L^a*(T i).width := le_mul_of_one_le_left hW.le hK
    have hw' := hw.trans hwidth
    have hfpoint := hpointF i lower upper hlu hu z w hw' (fun hz => hout (Or.inl hz))
    have hdpoint := hpointD i lower upper hlu hu z w hw' (fun hz => hout (Or.inr hz))
    have hfactor : (T i).width ≤ 4*(L^a*(T i).width) := by nlinarith
    have hderiv := (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans hdpoint
    calc
      _ ≤ L^(2*p+2)*((T i).weight (L^a) (D:ℝ) z)^8+
          L^(2*p+2)*((T i).weight (L^a) (D:ℝ) z)^8 := add_le_add hfpoint hderiv
      _ = 2*L^(2*p+2)*((T i).weight (L^a) (D:ℝ) z)^8 := by ring
      _ ≤ L*L^(2*p+2)*((T i).weight (L^a) (D:ℝ) z)^8 := by gcongr
      _ = _ := by
        have heq : L*L^(2*p+2) = L^(2*p+3) := by
          conv_lhs => lhs; rw [← Real.rpow_one L]
          rw [← Real.rpow_add hL0]
          congr 1
          ring
        rw [heq]

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
