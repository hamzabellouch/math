import OAI.Geometry.SurfaceImmersion.Atlas.WeightedCoefficientVariation
import OAI.Geometry.SurfaceImmersion.Correction.WeightedJetExpressions

namespace OAI

/-! A first-variation estimate for every finite higher-jet polynomial.
Its scale exponent is fixed by the polynomial, independently of output order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_plain_jet {U : Set Base} (hU : IsOpen U) {H : Base → Space}
    (hH : ContDiff ℝ ∞ H) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (m : ℕ) (w : List (Fin 2)) (a : Fin 4)
    (hb : WeightedBound U s (m + w.length) C H) :
    WeightedBound U s m (C / s ^ w.length) (jet H w a) := by
  have hc := hb.component hU.uniqueDiffOn hs.le hC hH.contDiffOn a
  have hcw : WeightedBound U s (m + (w.map coordinateVector).length) C (fun p => H p a) := by
    simpa only [List.length_map] using hc
  change WeightedBound U s m (C / s ^ w.length)
    (iteratedDirectional (w.map coordinateVector) (fun x => H x a))
  simpa only [List.length_map] using hcw.iteratedDirectional hU hs hC
    (contDiff_pi.mp hH a).contDiffOn (w.map coordinateVector)
    (fun v hv => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact norm_coordinateVector_le i) m

namespace Expression

lemma order_ge_two (e : Expression) : 2 ≤ e.order := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => exact ih.trans (le_max_right _ _)
  | add _ _ ih _ => exact ih.trans (le_max_left _ _)

private lemma increase_loss {U : Set Base} {s D : ℝ} {m d p : ℕ} {f : Base → ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hD : 0 ≤ D) (hdp : d ≤ p)
    (hb : WeightedBound U s m (D / s ^ d) f) : WeightedBound U s m (D / s ^ p) f :=
  hb.mono_const (div_le_div_of_nonneg_left hD (pow_pos hs p)
    (pow_le_pow_of_le_one hs.le hs1 hdp))

theorem compact_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G H : Base → Space) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ G → ContDiff ℝ ∞ H →
      Set.MapsTo (lowJet G) U K →
      WeightedBound U s (m + e.order) B (lowJet G) →
      WeightedBound U s (m + e.order) C H →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D * C / s ^ (e.loss + e.order))
          (fun p => e.variation G H (p, t)) := by
  induction e with
  | coeff c =>
    obtain ⟨D, hD, hb⟩ := compact_coefficient_variation hU hO hK hKO he m B hB
    refine ⟨D, hD, ?_⟩
    intro G H s C hs hs1 hC hG hH hGK hGb hHb t ht
    exact hb G H s C hs hs1 hC hG hH hGK (hGb.mono_order (by simp [order])) hHb t ht
  | atom w a e ih =>
    obtain ⟨D, hD, hb⟩ := ih he
    obtain ⟨A, hA, ha⟩ := compact_expression_bound hU hO hK hKO e he m B hB
    refine ⟨2 ^ m * A + 2 ^ m * B * D, by positivity, ?_⟩
    intro G H s C hs hs1 hC hG hH hGK hGb hHb t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have htail := ha G s hs hs1 hG hGK (hGb.mono_order (by simp only [order]; omega)) t ht
    have hvar := hb G H s C hs hs1 hC hG hH hGK
      (hGb.mono_order (by simp only [order]; omega)) (hHb.mono_order (by simp only [order]; omega)) t ht
    have hhjet := weighted_plain_jet hU hH hs hC m w a
      (hHb.mono_order (by simp only [order]; omega))
    have hgjet := weighted_actual_jet hU hG hs (zero_le_one.trans hB) m w a
      (hGb.mono_order (by simp only [order]; omega))
    have hfirst := hhjet.mul_real hU.uniqueDiffOn hs.le (by positivity) (by positivity)
      (jet_smooth hH w a).contDiffOn (parameter_smooth (e := e) hG hQ he t) htail
    have hsecond := hgjet.mul_real hU.uniqueDiffOn hs.le (by positivity) (by positivity)
      (jet_smooth hG w a).contDiffOn
      ((variation_smooth (e := e) hO hG hH hQ he).comp
        (contDiffOn_id.prodMk contDiffOn_const) (fun _ hp => ⟨hp, Set.mem_univ t⟩)) hvar
    have hfirst' : WeightedBound U s m ((2 ^ m * A * C) / s ^ (w.length + e.loss))
        (fun p => jet H w a p * e.eval G (p, t)) := by
      convert hfirst using 1
      rw [pow_add]
      ring
    have hsecond' : WeightedBound U s m
        ((2 ^ m * B * D * C) / s ^ ((w.length - 2) + (e.loss + e.order)))
        (fun p => jet G w a p * e.variation G H (p, t)) := by
      convert hsecond using 1 <;> first | rfl | rw [pow_add]; ring
    have hp1 := increase_loss hs hs1 (by positivity : 0 ≤ 2 ^ m * A * C)
      (show w.length + e.loss ≤ (atom w a e).loss + (atom w a e).order by
        have hn := order_ge_two e
        simp only [loss, order]
        omega) hfirst'
    have hp2 := increase_loss hs hs1 (by positivity : 0 ≤ 2 ^ m * B * D * C)
      (show (w.length - 2) + (e.loss + e.order) ≤ (atom w a e).loss + (atom w a e).order by
        simp only [loss, order]
        omega) hsecond'
    have hsum := hp1.add hU.uniqueDiffOn hs.le
      ((jet_smooth hH w a).contDiffOn.mul (parameter_smooth (e := e) hG hQ he t))
      ((jet_smooth hG w a).contDiffOn.mul
        ((variation_smooth (e := e) hO hG hH hQ he).comp
          (contDiffOn_id.prodMk contDiffOn_const) (fun _ hp => ⟨hp, Set.mem_univ t⟩))) hp2
    convert hsum using 1 <;> first | rfl | ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨A, hA, ha⟩ := ihf he.2
    refine ⟨D + A, add_nonneg hD hA, ?_⟩
    intro G H s C hs hs1 hC hG hH hGK hGb hHb t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have hd' := hd G H s C hs hs1 hC hG hH hGK
      (hGb.mono_order (by simp only [order]; omega)) (hHb.mono_order (by simp only [order]; omega)) t ht
    have ha' := ha G H s C hs hs1 hC hG hH hGK
      (hGb.mono_order (by simp only [order]; omega)) (hHb.mono_order (by simp only [order]; omega)) t ht
    have hd'' := increase_loss hs hs1 (mul_nonneg hD hC)
      (show e.loss + e.order ≤ (add e f).loss + (add e f).order by simp only [loss, order]; omega) hd'
    have ha'' := increase_loss hs hs1 (mul_nonneg hA hC)
      (show f.loss + f.order ≤ (add e f).loss + (add e f).order by simp only [loss, order]; omega) ha'
    have hsum := hd''.add hU.uniqueDiffOn hs.le
      ((variation_smooth (e := e) hO hG hH hQ he.1).comp
        (contDiffOn_id.prodMk contDiffOn_const) (fun _ hp => ⟨hp, Set.mem_univ t⟩))
      ((variation_smooth (e := f) hO hG hH hQ he.2).comp
        (contDiffOn_id.prodMk contDiffOn_const) (fun _ hp => ⟨hp, Set.mem_univ t⟩)) ha''
    convert hsum using 1 <;> first | rfl | ring

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
