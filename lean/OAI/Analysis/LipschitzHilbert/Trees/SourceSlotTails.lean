import OAI.Analysis.LipschitzHilbert.Trees.SourceCenteredSquareTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceCenteredMaskedVariation

namespace OAI

/-! Fixed slope slots are summed before taking the source square or
variation. Only the fixed slot count enters the union bound; empty
slots are allowed. The polynomial threshold and exponential rate
absorb this count uniformly before any packet family is chosen. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal FourierTransform
namespace LipschitzHilbert

/-- The square of the recombined positive scales costs the sum of the
individual slot squares, with constant one. -/
theorem source_slot_square_le {B N : ℕ} (f : Fin B → Fin N → ℝ) :
    Real.sqrt (∑ j, (∑ b, f b j)^2) ≤
      ∑ b, Real.sqrt (∑ j, f b j^2) := by
  let v (b : Fin B) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (f b)
  have hv (b : Fin B) : ‖v b‖ = Real.sqrt (∑ j, f b j^2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [v,Real.norm_eq_abs,sq_abs]
  have hs : ‖∑ b, v b‖ = Real.sqrt (∑ j, (∑ b, f b j)^2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [WithLp.ofLp_sum,Finset.sum_apply,v,Real.norm_eq_abs,sq_abs]
  rw [← hs]
  exact (norm_sum_le _ _).trans_eq (by simp only [hv])

/-- Recombining slots before partial sums does not enlarge cubic
variation beyond the sum of the separate slot variations. -/
theorem source_slot_packet_variation_le {B N : ℕ} {E : Type*}
    [NormedAddCommGroup E] (f : Fin B → Fin N → E) :
    cubicVariation (packetPartialSum (fun j => ∑ b, f b j)) N ≤
      ∑ b, cubicVariation (packetPartialSum (f b)) N := by
  have heq : packetPartialSum (fun j => ∑ b, f b j) =
      fun n => ∑ b, packetPartialSum (f b) n := by
    funext n
    unfold packetPartialSum
    calc
      _ = ∑ j : Fin N, ∑ b : Fin B, if j.val < n then f b j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = _ := Finset.sum_comm
  rw [heq]
  exact cubicVariation_finset_sum _ Finset.univ N

/-- A positive extra threshold absorbs every fixed finite slot count,
including zero slots. -/
theorem source_slot_bad_subset {B : ℕ} {X : Type*}
    (f : Fin B → X → ℝ) (F : X → ℝ) {small large : ℝ}
    (_hsmall : 0 < small) (hlarge : (B:ℝ)*small < large)
    (hF : ∀ x, |F x| ≤ ∑ b, |f b x|) :
    {x | large ≤ |F x|} ⊆ ⋃ b, {x | small ≤ |f b x|} := by
  classical
  intro x hx
  by_contra hn
  have hpoint (b : Fin B) : |f b x| ≤ small := by
    have h : ¬ small ≤ |f b x| := by
      intro hb
      exact hn (Set.mem_iUnion.mpr ⟨b,hb⟩)
    exact (lt_of_not_ge h).le
  have hsum : (∑ b, |f b x|) ≤ (B:ℝ)*small := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      (Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b))
  exact (not_le_of_gt (((hF x).trans hsum).trans_lt hlarge)) hx

/-- General finite-slot union estimate, with an arbitrary reference
mass (in the application it is the physical interval length). -/
theorem source_slot_tail {B : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Fin B → X → ℝ) (F : X → ℝ)
    {small large : ℝ} (hsmall : 0 < small)
    (hlarge : (B:ℝ)*small < large) (hF : ∀ x, |F x| ≤ ∑ b, |f b x|)
    (δ mass : ℝ≥0∞) (htail : ∀ b, μ {x | small ≤ |f b x|} ≤ δ*mass) :
    μ {x | large ≤ |F x|} ≤ (B:ℝ≥0∞)*δ*mass := by
  apply (measure_mono (source_slot_bad_subset f F hsmall hlarge hF)).trans
  calc
    _ ≤ ∑ b : Fin B, μ {x | small ≤ |f b x|} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _b : Fin B, δ*mass := Finset.sum_le_sum (fun b _ => htail b)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

/-- The constants are chosen before the slot functions, underlying
space or interval. One polynomial power and one exponential unit pay
for the fixed number of slots. -/
theorem eventually_source_fixed_slot_tail (B : ℕ) (a J : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X)
      (f : Fin B → X → ℝ) (F : X → ℝ) (mass : ℝ≥0∞),
      (∀ x, |F x| ≤ ∑ b, |f b x|) →
      (∀ b, μ {x | L^a ≤ |f b x|} ≤
        ENNReal.ofReal (Real.exp (-(J+1)*L))*mass) →
      μ {x | L^(a+1) ≤ |F x|} ≤ ENNReal.ofReal (Real.exp (-J*L))*mass := by
  filter_upwards [eventually_gt_atTop (max (B:ℝ) 0),
    eventually_source_polynomial_exp ((B:ℝ)+1) 0 J (by positivity)] with L hL hdecay
  have hL0 : 0 < L := (le_max_right _ _).trans_lt hL
  have hBL : (B:ℝ) < L := (le_max_left _ _).trans_lt hL
  have hthreshold : (B:ℝ)*L^a < L^(a+1) := by
    calc
      _ < L*L^a := mul_lt_mul_of_pos_right hBL (Real.rpow_pos_of_pos hL0 _)
      _ = L^a*L^(1:ℝ) := by rw [Real.rpow_one,mul_comm]
      _ = _ := (Real.rpow_add hL0 _ _).symm
  have hdecay' : (B:ℝ)*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
    apply (mul_le_mul_of_nonneg_right (show (B:ℝ) ≤ B+1 by linarith)
      (Real.exp_pos _).le).trans
    simpa only [Real.rpow_zero,mul_one] using hdecay
  intro X _ μ f F mass hF htail
  apply (source_slot_tail μ f F (Real.rpow_pos_of_pos hL0 _) hthreshold hF
    (ENNReal.ofReal (Real.exp (-(J+1)*L))) mass htail).trans
  have hc : (B:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(J+1)*L)) ≤
      ENNReal.ofReal (Real.exp (-J*L)) := by
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg B),ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal hdecay'
  exact mul_le_mul' hc le_rfl

end LipschitzHilbert

namespace LipschitzHilbert.SourceLatticePacket

/-- The actual centered positive squares of all narrow-label slots
have one physical exceptional threshold. Each slot may have a different
item type, including an empty item type at any scale. -/
theorem physical_centered_square_slot_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin B → Fin N → Type)
      [Fintype κ] [∀ b j, Fintype (ι b j)]
      (P : ∀ b, SourceLatticePacket N κ (ι b)),
      (∀ b, (P b).constant ≤ L^q) →
    ∀ (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j, 0 ≤ d j) → Monotone d →
      (∀ b j u k y xi, |xi| < (lo/(P b).topLength)*(2:ℝ)^j.val →
        𝓕 ((P b).raw 0 j u k y) xi = 0) →
      (∀ b j u k y xi, (hi/(P b).topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P b).raw 0 j u k y) xi = 0) →
    ∀ (s t y u H : ℝ), 0 < H → (∀ b j (_i : ι b j), (P b).length j ≤ H) →
      Measurable (fun x => ∑ b, (P b).physicalCenteredSquare s t d v g y x) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+7) ≤ |∑ b, (P b).physicalCenteredSquare s t d v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_centered_square_tail hVariation hlo hhi q (J+1) hq (by linarith),
    eventually_source_fixed_slot_tail B (2*q+6) J] with L htail hslots
  intro N κ ι _ _ P hP d v hv g hg hg1 hd hmono hlow hhigh s t y u H hH hwidth
  have hs (b : Fin B) := htail N κ (ι b) (P b) (hP b) d v hv g hg hg1 hd hmono
    (hlow b) (hhigh b) s t y u H hH (hwidth b)
  refine ⟨Finset.measurable_sum _ (fun b _ => (hs b).1),?_⟩
  have h := hslots ℝ (volume.restrict (Ico u (u+H)))
    (fun b x => (P b).physicalCenteredSquare s t d v g y x)
    (fun x => ∑ b, (P b).physicalCenteredSquare s t d v g y x)
    (ENNReal.ofReal H) (fun x => Finset.abs_sum_le_sum_abs _ _) (fun b => (hs b).2)
  simpa only [show 2*q+6+1 = 2*q+7 by ring] using h

/-- The actual centered masked variations of the fixed narrow-label
slots have a common physical tail. Recombining their packet bands is
controlled by `source_slot_packet_variation_le`. -/
theorem physical_centered_masked_variation_slot_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin B → Fin N → Type)
      [Fintype κ] [∀ b j, Fintype (ι b j)]
      (P : ∀ b, SourceLatticePacket N κ (ι b)),
      (∀ b, (P b).constant ≤ L^q) →
    ∀ (c : ∀ b j, ι b j → κ → ℂ) (hc : ∀ b j u k, ‖c b j u k‖ ≤ 1)
      (alt : ∀ b j, ι b j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ b j u k,
        planarProfileConstant (alt b j u k) (2*(P b).order) ≤ (P b).profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j, 0 ≤ d j) → Monotone d →
      (∀ b j u k y xi, |xi| < (lo/(P b).topLength)*(2:ℝ)^j.val →
        𝓕 (((P b).frozenProfile (c b) (hc b)).raw 0 j u k y) xi = 0) →
      (∀ b j u k y xi, (hi/(P b).topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 (((P b).frozenProfile (c b) (hc b)).raw 0 j u k y) xi = 0) →
      (∀ b j u k y xi, |xi| < (lo/(P b).topLength)*(2:ℝ)^j.val →
        𝓕 (((P b).withProfile (alt b) (hAlt b)).raw 0 j u k y) xi = 0) →
      (∀ b j u k y xi, (hi/(P b).topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 (((P b).withProfile (alt b) (hAlt b)).raw 0 j u k y) xi = 0) →
    ∀ (T : ∀ b j, ι b j → SlopeBox) (t : ℝ),
      (∀ b j u, (P b).length j ≤ (T b j u).length) →
      (∀ b j u, |t-(T b j u).slope| ≤ cone*(T b j u).width/(P b).length j) →
    ∀ (y u H : ℝ), 0 < H → (∀ b j (_i : ι b j), (P b).length j ≤ H) →
      Measurable (fun x => ∑ b, (P b).physicalCenteredMaskedVariation
        (c b) (alt b) (hAlt b) d v g (T b) L A t y x) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+8) ≤ |∑ b, (P b).physicalCenteredMaskedVariation
          (c b) (alt b) (hAlt b) d v g (T b) L A t y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_centered_masked_variation_tail hVariation hlo hhi q (J+1)
    A cone hq (by linarith) hA hcone,
    eventually_source_fixed_slot_tail B (2*q+7) J] with L htail hslots
  intro N κ ι _ _ P hP c hc alt hAlt d v hv g hg hg1 hd hmono hAlow hAhigh hSlow hShigh
    T t hshort hcone' y u H hH hwidth
  have hs (b : Fin B) := htail N κ (ι b) (P b) (hP b) (c b) (hc b) (alt b) (hAlt b)
    d v hv g hg hg1 hd hmono (hAlow b) (hAhigh b) (hSlow b) (hShigh b)
    (T b) t (hshort b) (hcone' b) y u H hH (hwidth b)
  refine ⟨Finset.measurable_sum _ (fun b _ => (hs b).1),?_⟩
  have h := hslots ℝ (volume.restrict (Ico u (u+H)))
    (fun b x => (P b).physicalCenteredMaskedVariation
      (c b) (alt b) (hAlt b) d v g (T b) L A t y x)
    (fun x => ∑ b, (P b).physicalCenteredMaskedVariation
      (c b) (alt b) (hAlt b) d v g (T b) L A t y x)
    (ENNReal.ofReal H) (fun x => Finset.abs_sum_le_sum_abs _ _) (fun b => (hs b).2)
  simpa only [show 2*q+7+1 = 2*q+8 by ring] using h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
