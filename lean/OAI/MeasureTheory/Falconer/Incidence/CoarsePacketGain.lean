import OAI.MeasureTheory.Falconer.Estimates.GoodCoarseRows
import OAI.MeasureTheory.Falconer.Estimates.QuantitativePacketPoints
import OAI.MeasureTheory.Falconer.Incidence.LocalPencilPacketGain

namespace OAI

/-! Packet growth from actual coarse incidences and their weighted fine pencils. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem coarse_packet_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let D := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      let Lo := fun s : ℝ => Real.exp ((s-ε)*((n+2:ℕ):ℝ)*Real.log 2)
      let Up := fun s : ℝ => Real.exp ((s+ε)*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ (s t K KP KF m M mF MF L J B R : ℝ) (C : Finset (Space 2))
        (T P : Space 2 → Finset (Space 2))
        (V : Space 2 → Space 2 → Finset (Space 2)) (q : Space 2 → Space 2 → Space 2)
        (G : Space 2 → Finset (Space 2)),
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      1 ≤ K → 1 ≤ KP → 1 ≤ KF → 0 < m → 0 < L → 0 < mF → 0 < MF →
      0 < J → 0 < B → 1 ≤ R → C.Nonempty → InBoundedLineChart C →
      FiniteSeparatedAt (1/(2:ℝ)^(n+3)) C →
      NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) t K C →
      (∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
        InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^(n+3)) (T x) ∧
        NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) s K (T x) ∧
        ∀ a ∈ T x, TubeIncident (1/(2:ℝ)^(n+3)) x a) →
      ((C.biUnion T).card:ℝ) ≤ L →
      (∀ x ∈ C, (P x).Nonempty ∧
        (∀ p ∈ P x, |p 0-x 0| ≤ Δ ∧ |p 1-x 1| ≤ Δ) ∧
        NormalizedFiniteBallBound Δ t KP ((P x).image (localPacketPoint Δ (x 0) (x 1)))) →
      (∀ x ∈ C, ∀ p ∈ P x, mF ≤ ((V x p).card:ℝ) ∧ ((V x p).card:ℝ) ≤ MF ∧
        FiniteSeparatedAt (Δ^2) (V x p) ∧ NormalizedFiniteBallBound (Δ^2) s KF (V x p) ∧
        ∀ l ∈ V x p, |l 0| ≤ 1 ∧ TubeIncident (Δ^2) p l) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, dist l (q x l) ≤ Δ) →
      (∀ x ∈ C, ∀ a ∈ T x,
        ((∑ p ∈ P x, (V x p).card):ℝ) ≤ 2*J*B*(coarsePencilWeight (P x) (V x) (q x) a:ℝ)) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, l ∈ G (q x l)) →
      4*pencilEnergyCutoff (n+3) s t (50*K) M (m/50) C*
        (4*L/((m/50)*(C.card:ℝ)))^2*(2:ℝ)^(t-s) ≤ R →
      100*R ≤ D → 2 ≤ D →
      Lo s ≤ mF/(4*J*B) → KF*Δ^s*MF ≤ Up s → KF*(4*J*B*MF/mF) ≤ D/Δ^s →
      projectedSubsetSampleConstant n s t (25*K*(4:ℝ)^s) KP
        (mF/(4*J*B*(KF*Δ^s*MF))) ≤ D →
      ∃ a ∈ C.biUnion T,
        Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2) ≤ ((G a).card:ℝ) := by
  obtain ⟨ε,η,N0,hε,hη,hN0,hmain⟩ := centered_packet_gain_from_local_pencils hκ hκ1
  refine ⟨ε,η,N0,hε,hη,hN0,?_⟩
  intro n hn
  dsimp only
  intro s t K KP KF m M mF MF L J B R C T P V q G
    hs hs1 hgap ht hK hKP hKF hm hL hmF hMF hJ hB hR hC hCchart hCsep hCball
    hT hunion hP hV hnear hweight hG hfiber hrow hD hlo hup hreg hsample
  let Δ := 1/(2:ℝ)^n
  let D := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let Q := fun x => (P x).image (localPacketPoint Δ (x 0) (x 1))
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ1 : Δ ≤ 1 := (div_le_one (by positivity : (0:ℝ) < 2^n)).2
    (one_le_pow₀ (by norm_num))
  have hδΔ : Δ^2 ≤ Δ := by nlinarith only [hΔ,hΔ1]
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hst : s < t := by linarith only [hκ,hgap]
  obtain ⟨a,ha,Y,hY,_,hYball,c,hc⟩ := good_coarse_rows n hs0 hst
    (show 2*κ ≤ 1 by linarith only [hs,hs1]) hgap hK hKP hm hL hR
    C T Q hC hCchart hCsep hCball hT (by
      intro x hx
      exact ⟨(hP x hx).1.image _,localPacketPoint_chart hΔ (P x) (hP x hx).2.1,(hP x hx).2.2⟩)
    hunion hfiber
  have chooseA (x : Space 2) (hx : x ∈ C ∧ a ∈ T x) :=
    quantitative_packet_points (pow_pos hΔ 2) hΔ hδΔ hs0 hKF hmF hMF hJ hB
      (P x) (V x) (hP x hx.1).1 (q x) a (hnear x hx.1) (hV x hx.1) (hweight x hx.1 a hx.2)
  let A := fun x => if hx : x ∈ C ∧ a ∈ T x then Classical.choose (chooseA x hx) else ∅
  have hA (x : Space 2) (hx : x ∈ C ∧ a ∈ T x) := by
    have hh := Classical.choose_spec (chooseA x hx)
    have he : A x = Classical.choose (chooseA x hx) := dite_eq_left hx
    rw [← he] at hh
    exact hh
  have ha0 : |a 0| ≤ 1 := by
    obtain ⟨x,hx,hax⟩ := Finset.mem_biUnion.mp ha
    exact ((hT x hx).2.2.1 a hax).1
  refine ⟨a,ha,?_⟩
  apply hmain n hn s t (25*K*(4:ℝ)^s) KP (mF/(4*J*B*(KF*Δ^s*MF)))
    (-a 0) (a 1) Y (fun y => P (c y)) (fun y => A (c y)) (fun y => c y 1)
    (fun y p => (V (c y) p).filter fun l => q (c y) l = a) (G a)
    hs hs1 hst (by positivity) (zero_le_one.trans hKP) (by positivity)
    (by simpa only [abs_neg] using ha0) hY (fun y hy => (hc y hy).2.2.1) hD hsample
  · intro y hy
    have hcy := hc y hy
    have hh := hA (c y) ⟨hcy.1,hcy.2.2.2.1⟩
    refine ⟨(hP (c y) hcy.1).1,hh.1,hh.2.2.1,?_,?_⟩
    · intro p hp
      simpa only [hcy.2.1] using (hP (c y) hcy.1).2.1 p hp
    · have he := hcy.2.2.2.2
      dsimp only [Q] at he
      rw [Finset.card_image_of_injective _ (localPacketPoint_injective hΔ _ _)] at he
      simpa only [hcy.2.1] using he
  · intro y hy p hp
    have hcy := hc y hy
    have hh := hA (c y) ⟨hcy.1,hcy.2.2.2.1⟩
    obtain ⟨_,hlo',hup',hsep',hball',hinc'⟩ := hh.2.2.2 p hp
    refine ⟨?_,hsep',?_,hlo.trans hlo',hup'.trans hup,?_⟩
    · intro l hl
      obtain ⟨hlV,hlq⟩ := Finset.mem_filter.mp hl
      simpa only [hlq] using hG (c y) hcy.1 p (hh.1 hp) l hlV
    · intro z r hr hr1
      exact (hball' z r hr hr1).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hreg (Real.rpow_nonneg ((pow_nonneg hΔ.le 2).trans hr) _))
        (Nat.cast_nonneg _))
    · intro l hl
      simpa only [sub_eq_add_neg] using hinc' l hl
  · intro u r hr hr1
    have hscale : 1/(2:ℝ)^(n+3) = Δ/8 := by
      dsimp [Δ]
      rw [pow_add]
      norm_num
      ring
    have hr' : 1/(2:ℝ)^(n+3) ≤ r := by rw [hscale]; linarith only [hr,hΔ]
    exact (hYball u r hr' hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg (le_trans (by positivity : 0 ≤ (1/(2:ℝ)^n)/4) hr) _))
      (Nat.cast_nonneg _))

end Falconer

end OAI
