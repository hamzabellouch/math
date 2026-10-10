import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedCoefficient
import OAI.Analysis.LipschitzHilbert.Trees.SourceCrossConcentration

namespace OAI

/-! Concentration for the original finite labeled top families. Slotting
is used only inside the local concentration theorem. The conclusion is
indexed by the original tops, before any witness or direction-counting
argument, and the fixed slot factor is absorbed explicitly. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LipschitzHilbert

structure SourceLabeledTopGeometry {N : ℕ} {κ : Type} {Label : Fin N → Type}
    {Item : ∀ j, Label j → Type} [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item) (T : SlopeBox) (K : ℝ) (D : ℕ) : Prop where
  length_le : P.topLength ≤ K * T.length
  width_le : P.width ≤ K * T.width
  centerX_le : ∀ j l u, |P.actualX j l u - T.x| + P.length j ≤ K * T.length
  centerZ_le : ∀ j l u,
    |P.actualZ j l u - (T.y - T.slope * T.x)| + P.width ≤ K * T.width
  order_le : 3 + 2 * (8 * D + 1) ≤ P.order
  scale_eq : P.scale = 4 * (K * T.width)

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem slotted_topGeometry (P : SourceLabeledLattice N κ Label Item)
    {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)
    {T : SlopeBox} {K : ℝ} {D : ℕ} (G : SourceLabeledTopGeometry P T K D) (b : Fin B) :
    SourceLatticeTopGeometry (P.slotted hcard b) T K D where
  length_le := G.length_le
  width_le := G.width_le
  centerX_le := by
    intro j p
    rw [P.slotted_actualX hcard, P.slotted_length hcard]
    exact G.centerX_le j p.1.1 p.1.2
  centerZ_le := by
    intro j p
    rw [P.slotted_actualZ hcard]
    exact G.centerZ_le j p.1.1 p.1.2
  order_le := G.order_le
  scale_eq := G.scale_eq

private theorem slot_decay {B : ℕ} {J L : ℝ} (hB : (B : ℝ) ≤ L) :
    (B : ℝ) * Real.exp (-(J + 1) * L) ≤ Real.exp (-J * L) := by
  have hb : (B : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  calc
    _ ≤ Real.exp L * Real.exp (-(J + 1) * L) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = Real.exp (-J * L) := by rw [← Real.exp_add]; congr 1; ring

private theorem sum_joint_norm_le {B : ℕ} {E : Type*} [NormedAddCommGroup E]
    (F DF : Fin B → E) {W C : ℝ} (hW : 0 ≤ W)
    (h : ∀ b, ‖F b‖ + W * ‖DF b‖ ≤ C) :
    ‖∑ b, F b‖ + W * ‖∑ b, DF b‖ ≤ (B : ℝ) * C := by
  calc
    _ ≤ (∑ b, ‖F b‖) + W * (∑ b, ‖DF b‖) :=
      add_le_add (norm_sum_le _ _) (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hW)
    _ = ∑ b, (‖F b‖ + W * ‖DF b‖) := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ _b : Fin B, C := Finset.sum_le_sum (fun b _ => h b)
    _ = _ := by simp

theorem source_labeled_concentration (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hcStar : 0 ≤ cStar) (hCEta : 0 ≤ CEta)
    (hgap : cStar < cEta * cb) (J a p : ℝ) (D B : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ (B : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (Label : ∀ i, Fin (N i) → Type)
        (Item : ∀ i j, Label i j → Type) [∀ i j l, Fintype (Item i j l)]
        (P : ∀ i, SourceLabeledLattice (N i) κ (Label i) (Item i))
        (_hcard : ∀ i j, ((P i).labels j).card ≤ B),
      (∀ i, (P i).constant ≤ L ^ p) →
      ∀ (alt : ∀ i j (l : (P i).labels j), Item i j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ i j l u k,
          planarProfileConstant (alt i j l u k) (2 * (P i).order) ≤ (P i).profileBound)
        (cutoff : ∀ i, Fin (N i) → ℝ) (v : τ → ℝ × ℝ → ℝ),
      (∀ i, Measurable (v i)) →
      ∀ (g : τ → ℝ × ℝ → EuclideanSpace ℂ κ), (∀ i, Measurable (g i)) →
      (∀ i z, ‖g i z‖ ≤ 1) → (∀ i, Monotone (cutoff i)) →
      ∀ (T : τ → SlopeBox) (w : ℝ), 0 < w →
      (∀ i j l u k ξ η, planarAngularFourier ((P i).physicalPacket (T i).slope j l u k)
          (ξ, η) ≠ 0 →
        |ξ + ((T i).slope + (P i).rowSlope j l) * η| ≤ cStar / (P i).length j ∧
          cEta ≤ w * η ∧ w * η ≤ CEta) →
      (∀ i j l u k ξ η,
        planarAngularFourier (((P i).withProfile (alt i) (hAlt i)).physicalPacket
          (T i).slope j l u k) (ξ, η) ≠ 0 →
        |ξ + ((T i).slope + (P i).rowSlope j l) * η| ≤ cStar / (P i).length j ∧
          cEta ≤ w * η ∧ w * η ≤ CEta) →
      (∀ i j (l : (P i).labels j) (_u : Item i j l),
        cb * w / (P i).length j ≤ |(P i).rowSlope j l| ∧
          |(P i).rowSlope j l| ≤ Cb * w / (P i).length j) →
      (∀ i, SourceLabeledTopGeometry (P i) (T i) (L ^ a) D) →
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J * L) * (∑ i, (T i).area)) ∧
        ∀ i lower upper, lower ≤ upper → upper ≤ N i → ∀ z shift,
          |shift| ≤ (T i).width → z ∉ bad →
          let F := fun x y => ((P i).withProfile (alt i) (hAlt i)).rawInterval
            ((P i).physicalCoefficient (T i).slope (cutoff i) (v i) (g i))
            0 lower upper x y
          ‖F z.1 ((z.2 - (T i).slope * z.1) + shift)‖ +
            (T i).width * ‖covariantSignal (P i).frequency (fun k t => F z.1 t k)
              ((z.2 - (T i).slope * z.1) + shift)‖ ≤
                L ^ (2 * p + 6) * ((T i).weight (L ^ a) (D : ℝ) z) ^ 8 := by
  classical
  obtain ⟨L1, hL1, hconc⟩ := SourceLatticePacket.source_cross_concentration hL
    cStar cEta CEta cb Cb hcEta hcb hCb hcStar hCEta hgap (J + 1) a p D (by linarith) ha hp
  refine ⟨max L1 B, hL1.trans (le_max_left _ _), le_max_right _ _, ?_⟩
  intro L hLL τ κ _ _ N Label Item _ P hcard hP alt hAlt cutoff v hv g hg hg1 hcut T w hw
    hspectrum haltSpectrum hselector G
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) (hL1.trans ((le_max_left _ _).trans hLL))
  have hBL : (B : ℝ) ≤ L := (le_max_right _ _).trans hLL
  let N' : τ × Fin B → ℕ := fun q => N q.1
  let Item' : ∀ q : τ × Fin B, Fin (N' q) → Type :=
    fun q => (P q.1).SlotItem (hcard q.1) q.2
  let P' : ∀ q : τ × Fin B, SourceLatticePacket (N' q) κ (Item' q) :=
    fun q => (P q.1).slotted (hcard q.1) q.2
  let alt' := fun (q : τ × Fin B) => (P q.1).slottedAlt (hcard q.1) (alt q.1) q.2
  have hAlt' : ∀ q j u k,
      planarProfileConstant (alt' q j u k) (2 * (P' q).order) ≤ (P' q).profileBound :=
    fun q => (P q.1).slottedAlt_bound (hcard q.1) (alt q.1) (hAlt q.1) q.2
  have hp' (q : τ × Fin B) : (P' q).constant ≤ L ^ p := by
    simpa only [P', slotted_constant] using hP q.1
  have hv' (q : τ × Fin B) : Measurable (fun z => v q.1 (sourceReferenceToPhysical (T q.1).slope z)) :=
    (hv q.1).comp (sourceReferenceToPhysical (T q.1).slope).measurable
  have hg' (q : τ × Fin B) : Measurable (fun z => g q.1 (sourceReferenceToPhysical (T q.1).slope z)) :=
    (hg q.1).comp (sourceReferenceToPhysical (T q.1).slope).measurable
  have hspec' : ∀ q j u k ξ η,
      planarAngularFourier ((P' q).physicalPacket (T q.1).slope j u k) (ξ, η) ≠ 0 →
      |ξ + ((T q.1).slope + (P' q).rowSlope j) * η| ≤ cStar / (P' q).length j ∧
        cEta ≤ w * η ∧ w * η ≤ CEta := by
    intro q
    exact (P q.1).slotted_spectrum (hcard q.1) (T q.1).slope w cStar cEta CEta
      (hspectrum q.1) q.2
  have haltSpec' : ∀ q j u k ξ η,
      planarAngularFourier (((P' q).withProfile (alt' q) (hAlt' q)).physicalPacket
        (T q.1).slope j u k) (ξ, η) ≠ 0 →
      |ξ + ((T q.1).slope + (P' q).rowSlope j) * η| ≤ cStar / (P' q).length j ∧
        cEta ≤ w * η ∧ w * η ≤ CEta := by
    intro q j u k ξ η hn
    change planarAngularFourier ((((P q.1).slotted (hcard q.1) q.2).withProfile
      ((P q.1).slottedAlt (hcard q.1) (alt q.1) q.2)
      ((P q.1).slottedAlt_bound (hcard q.1) (alt q.1) (hAlt q.1) q.2)).physicalPacket
        (T q.1).slope j u k) (ξ, η) ≠ 0 at hn
    rw [(P q.1).slotted_alt_physicalPacket (hcard q.1) (alt q.1) (hAlt q.1)] at hn
    simpa only [P', (P q.1).slotted_rowSlope (hcard q.1) q.2 j u, slotted_length] using
      haltSpectrum q.1 j u.1.1 u.1.2 k ξ η hn
  have hsel' : ∀ q j (_u : Item' q j), cb * w / (P' q).length j ≤ |(P' q).rowSlope j| ∧
      |(P' q).rowSlope j| ≤ Cb * w / (P' q).length j := by
    intro q
    exact (P q.1).slotted_selector (hcard q.1) w cb Cb (hselector q.1) q.2
  have G' (q : τ × Fin B) : SourceLatticeTopGeometry (P' q) (T q.1) (L ^ a) D :=
    (P q.1).slotted_topGeometry (hcard q.1) (G q.1) q.2
  obtain ⟨bad, hbad, harea, hpoint⟩ := hconc L ((le_max_left _ _).trans hLL)
    (τ × Fin B) κ N' Item' P' hp' alt' hAlt' (fun q => cutoff q.1)
    (fun q z => v q.1 (sourceReferenceToPhysical (T q.1).slope z)) hv'
    (fun q z => g q.1 (sourceReferenceToPhysical (T q.1).slope z)) hg'
    (fun q z => hg1 q.1 _) (fun q => hcut q.1) (fun q => T q.1) w hw
    hspec' haltSpec' hsel' G'
  have hsumarea : (∑ q : τ × Fin B, (T q.1).area) = (B : ℝ) * ∑ i, (T i).area := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  refine ⟨bad, hbad, harea.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · rw [hsumarea]
    have hs : 0 ≤ ∑ i, (T i).area := Finset.sum_nonneg fun i _ => (T i).area_pos.le
    calc
      _ = ((B : ℝ) * Real.exp (-(J + 1) * L)) * ∑ i, (T i).area := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (slot_decay hBL) hs
  intro i lower upper hlu hu z shift hshift hout
  dsimp only
  let Q := (P i).withProfile (alt i) (hAlt i)
  let coeff := (P i).physicalCoefficient (T i).slope (cutoff i) (v i) (g i)
  let F := fun b : Fin B => (Q.slotted (hcard i) b).rawInterval
    (fun j u => coeff j u.1.1 u.1.2) 0 lower upper z.1
  let y := (z.2 - (T i).slope * z.1) + shift
  have hscale : Q.scale ≠ 0 := by
    change (P i).scale ≠ 0
    rw [(G i).scale_eq]
    exact ne_of_gt (mul_pos (by norm_num) (mul_pos (Real.rpow_pos_of_pos hLpos _) (T i).width_pos))
  have hsum : (∑ b, F b y) = Q.rawInterval coeff 0 lower upper z.1 y :=
    Q.sum_slotted_rawInterval (hcard i) coeff 0 lower upper z.1 y
  have hd : (∑ b, covariantSignal (P i).frequency (fun k t => F b t k) y) =
      covariantSignal (P i).frequency (fun k t => Q.rawInterval coeff 0 lower upper z.1 t k) y :=
    Q.sum_slotted_covariant (hcard i) hscale coeff lower upper z.1 y
  have hb (b : Fin B) : ‖F b y‖ + (T i).width *
      ‖covariantSignal (P i).frequency (fun k t => F b t k) y‖ ≤
      L ^ (2 * p + 5) * ((T i).weight (L ^ a) (D : ℝ) z) ^ 8 := by
    have h := hpoint (i, b) lower upper hlu hu z shift hshift hout
    have hc : (P' (i, b)).family.mainCoefficient (cutoff i)
        (fun z => v i (sourceReferenceToPhysical (T i).slope z))
        (fun z => g i (sourceReferenceToPhysical (T i).slope z)) =
        (fun j u => coeff j u.1.1 u.1.2) := by
      funext j u
      exact (P i).slotted_mainCoefficient_physical (hcard i) b (T i).slope
        (cutoff i) (v i) (g i) j u
    let A := fun x y => ((P' (i, b)).withProfile (alt' (i, b)) (hAlt' (i, b))).rawInterval
      ((P' (i, b)).family.mainCoefficient (cutoff i)
        (fun z => v i (sourceReferenceToPhysical (T i).slope z))
        (fun z => g i (sourceReferenceToPhysical (T i).slope z))) 0 lower upper x y
    change ‖A z.1 y‖ + (T i).width *
      ‖covariantSignal (P i).frequency (fun k t => A z.1 t k) y‖ ≤ _ at h
    have hA : A z.1 = F b := by
      funext t
      dsimp only [A]
      rw [hc]
      change (((P i).slotted (hcard i) b).withProfile
        ((P i).slottedAlt (hcard i) (alt i) b)
        ((P i).slottedAlt_bound (hcard i) (alt i) (hAlt i) b)).rawInterval
          (fun j u => coeff j u.1.1 u.1.2) 0 lower upper z.1 t = _
      rw [← (P i).withProfile_slotted (hcard i) (alt i) (hAlt i) b]
      rfl
    rw [hA] at h
    exact h
  have hn := sum_joint_norm_le (fun b => F b y)
    (fun b => covariantSignal (P i).frequency (fun k t => F b t k) y) (T i).width_pos.le hb
  rw [hsum, hd] at hn
  apply hn.trans
  have hexp : (B : ℝ) * L ^ (2 * p + 5) ≤ L ^ (2 * p + 6) := by
    calc
      _ ≤ L * L ^ (2 * p + 5) := mul_le_mul_of_nonneg_right hBL (Real.rpow_nonneg hLpos.le _)
      _ = L ^ (2 * p + 6) := by
        calc
          _ = L ^ (1 : ℝ) * L ^ (2 * p + 5) := by rw [Real.rpow_one]
          _ = L ^ (1 + (2 * p + 5)) := (Real.rpow_add hLpos _ _).symm
          _ = _ := by congr 1; ring
  calc
    _ = ((B : ℝ) * L ^ (2 * p + 5)) * ((T i).weight (L ^ a) (D : ℝ) z) ^ 8 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
