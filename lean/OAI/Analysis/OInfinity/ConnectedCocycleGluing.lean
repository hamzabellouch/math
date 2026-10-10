import OAI.Analysis.OInfinity.ClockCocycleFamily

namespace OAI

/-! # Connected gluing of the actual finite cocycle paths

The paths for all finite cocycle coefficients use one partition. This lets
the weighted sum be deformed continuously to one, with both Gram defects
controlled throughout the deformation. The cyclic seam is retained exactly.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private lemma glued_product_commutator (u v : unitary E) (e : E) :
    ‖((u * v : unitary E) : E) * e - e * (u * v : unitary E)‖ ≤
      ‖(u : E) * e - e * (u : E)‖ + ‖(v : E) * e - e * (v : E)‖ := by
  have hid : ((u * v : unitary E) : E) * e - e * (u * v : unitary E) =
      ((u : E) * e - e * (u : E)) * (v : E) +
        (u : E) * ((v : E) * e - e * (v : E)) := by
    change ((u : E) * (v : E)) * e - e * ((u : E) * (v : E)) = _
    noncomm_ring
  rw [hid]
  simpa only [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul] using
    norm_add_le (((u : E) * e - e * (u : E)) * (v : E))
      ((u : E) * ((v : E) * e - e * (v : E)))

/-- Transport a commutator through one step of the actual endomorphism. -/
lemma clock_endomorphism_commutator (φ : E →⋆ₙₐ[ℂ] E)
    (α : unitary E →* unitary E) (hα : ∀ u, (α u : E) = φ u)
    (u : unitary E) (e f : E) (C η : ℝ)
    (hc : ‖(u : E) * e - e * (u : E)‖ ≤ C)
    (he : ‖φ e - f‖ ≤ η) :
    ‖(α u : E) * f - f * (α u : E)‖ ≤ C + 2 * η := by
  have hid : (α u : E) * f - f * (α u : E) =
      φ ((u : E) * e - e * (u : E)) +
        ((α u : E) * (f - φ e) - (f - φ e) * (α u : E)) := by
    rw [map_sub, map_mul, map_mul, ← hα]
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖φ ((u : E) * e - e * (u : E))‖ +
        ‖(α u : E) * (f - φ e) - (f - φ e) * (α u : E)‖ := norm_add_le _ _
    _ ≤ ‖(u : E) * e - e * (u : E)‖ +
        (‖(α u : E) * (f - φ e)‖ + ‖(f - φ e) * (α u : E)‖) :=
      add_le_add (NonUnitalStarAlgHom.norm_apply_le φ _) (norm_sub_le _ _)
    _ = ‖(u : E) * e - e * (u : E)‖ + 2 * ‖φ e - f‖ := by
      rw [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary,
        norm_sub_rev f]
      ring
    _ ≤ _ := by linarith

lemma clock_iterate_commutator {N : ℕ} (φ : E →⋆ₙₐ[ℂ] E)
    (α : unitary E →* unitary E) (hα : ∀ u, (α u : E) = φ u)
    (e : ZMod N → E) (η C : ℝ)
    (hs : ∀ j, ‖φ (e j) - e (j + 1)‖ ≤ η)
    (u : unitary E) (hc : ∀ j, ‖(u : E) * e j - e j * (u : E)‖ ≤ C)
    (n : ℕ) (j : ZMod N) :
    ‖((α^[n]) u : E) * e j - e j * ((α^[n]) u : E)‖ ≤ C + 2 * n * η := by
  induction n generalizing j with
  | zero => simpa using hc j
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have ht := clock_endomorphism_commutator φ α hα ((α^[n]) u)
        (e (j - 1)) (e j) (C + 2 * n * η) η (ih (j - 1))
        (by simpa using hs (j - 1))
      convert ht using 1
      push_cast
      ring

/-- Move from a chosen sampling time to the terminal time. -/
def clockTailTime (a t : unitInterval) : unitInterval :=
  ⟨a + t * (1 - a), by
    constructor
    · exact add_nonneg a.2.1 (mul_nonneg t.2.1 (sub_nonneg.mpr a.2.2))
    · nlinarith [a.2.1, a.2.2, t.2.1, t.2.2]⟩

lemma clockTailTime_continuous (a : unitInterval) : Continuous (clockTailTime a) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : unitInterval => (a : ℝ) + (t : ℝ) * (1 - a))
  fun_prop

@[simp] lemma clockTailTime_zero (a : unitInterval) : clockTailTime a 0 = a := by
  apply Subtype.ext
  change (a : ℝ) + 0 * (1 - a) = a
  ring

@[simp] lemma clockTailTime_one (a : unitInterval) : clockTailTime a 1 = 1 := by
  apply Subtype.ext
  change (a : ℝ) + 1 * (1 - a) = 1
  ring

/-- Coefficient contraction using the two paths on the same partition. -/
def clockCoefficientContraction (α : unitary E →* unitary E) (hα : Continuous α)
    {u v : unitary E} (p : Path u 1) (q : Path v 1) (a : unitInterval) (j : ℕ) :
    Path (u * (α^[j]) (q a)) 1 where
  toFun t := p t * (α^[j]) (q (clockTailTime a t))
  continuous_toFun := p.continuous.mul
    ((hα.iterate j).comp (q.continuous.comp (clockTailTime_continuous a)))
  source' := by simp only [clockTailTime_zero, p.source]
  target' := by simp only [clockTailTime_one, p.target, q.target,
    unitaryHom_iterate_one, mul_one]

lemma clockCoefficientContraction_commutator {N : ℕ}
    (φ : E →⋆ₙₐ[ℂ] E) (α : unitary E →* unitary E)
    (hα : ∀ u, (α u : E) = φ u) (hcont : Continuous α)
    (e : ZMod N → E) (η C : ℝ)
    (hs : ∀ k, ‖φ (e k) - e (k + 1)‖ ≤ η)
    {u v : unitary E} (p : Path u 1) (q : Path v 1)
    (hp : ∀ t k, ‖(p t : E) * e k - e k * (p t : E)‖ ≤ C)
    (hq : ∀ t k, ‖(q t : E) * e k - e k * (q t : E)‖ ≤ C)
    (a t : unitInterval) (j : ℕ) (k : ZMod N) :
    ‖(clockCoefficientContraction α hcont p q a j t : E) * e k -
      e k * (clockCoefficientContraction α hcont p q a j t : E)‖ ≤
        2 * C + 2 * j * η := by
  have hb := clock_iterate_commutator φ α hα e η C hs
    (q (clockTailTime a t)) (hq _) j k
  exact (glued_product_commutator (p t) ((α^[j]) (q (clockTailTime a t))) (e k)).trans
    (by linarith [hp t k])

/-- Small diagonal commutators throughout a coefficient homotopy give a
connected polar correction of its initial weighted sum. -/
lemma exists_connected_rohlin_polar_tolerance [Nontrivial E]
    {I : Type*} [Fintype I] [DecidableEq I] (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (e : I → E),
      (∀ i, IsStarProjection (e i)) → (∑ i, e i) = 1 →
      (∀ i j, i ≠ j → e i * e j = 0) →
      ∀ (v : I → unitInterval → unitary E),
        (∀ i, Continuous (v i)) → (∀ i, v i 1 = 1) →
        (∀ t i, ‖(v i t : E) * e i - e i * (v i t : E)‖ ≤ δ) →
        ∃ u : unitary E, Joined (1 : unitary E) u ∧
          ‖(u : E) - finiteRohlinSum (fun i => v i 0) e‖ < ε := by
  obtain ⟨τ, hτ, hτ1, hpolar⟩ := exists_clockPolar_tolerance (E := E) ε hε
  let D : ℝ := (Fintype.card I : ℝ) * (2 * Real.sqrt (Fintype.card I) + 1) + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  let δ := τ / (2 * D)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hsmall : D * δ < τ := by
    have heq : D * δ = τ / 2 := by
      dsimp only [δ]
      field_simp [ne_of_gt hD]
    rw [heq]
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro e he hes heo v hv hv1 hc
  let z : unitInterval → E := fun t => finiteRohlinSum (fun i => v i t) e
  have hz : Continuous z := by
    unfold z finiteRohlinSum
    fun_prop
  have hgram (t : unitInterval) :
      ‖star (z t) * z t - 1‖ < τ ∧ ‖z t * star (z t) - 1‖ < τ := by
    have hi := finiteRohlinSum_isometry_defect_le (fun i => v i t) e
      (fun i => (he i).isSelfAdjoint.star_eq) (fun i => (he i).isIdempotentElem.eq)
      heo hes δ (hc t)
    have hf := finiteRohlinSum_coisometry_defect_le (fun i => v i t) e
      (fun i => (he i).isSelfAdjoint.star_eq) (fun i => (he i).isIdempotentElem.eq)
      heo hes δ (hc t)
    have hiD : (Fintype.card I : ℝ) * (2 * Real.sqrt (Fintype.card I) + 1) ≤ D := by
      dsimp only [D]; linarith
    have hfD : (Fintype.card I : ℝ) ≤ D := by
      dsimp only [D]
      nlinarith [Real.sqrt_nonneg (Fintype.card I),
        mul_nonneg (show (0 : ℝ) ≤ Fintype.card I by positivity)
          (Real.sqrt_nonneg (Fintype.card I))]
    exact ⟨hi.trans_lt ((mul_le_mul_of_nonneg_right hiD hδ.le).trans_lt hsmall),
      hf.trans_lt ((mul_le_mul_of_nonneg_right hfD hδ.le).trans_lt hsmall)⟩
  have hp (t : unitInterval) : clockPolarValue (z t) ∈ unitary E ∧
      ‖clockPolarValue (z t) - z t‖ < ε := hpolar _ (hgram t).1 (hgram t).2
  let w : unitInterval → unitary E := fun t => ⟨clockPolarValue (z t), (hp t).1⟩
  have hw : Continuous w := by
    apply Continuous.subtype_mk
    exact clockPolarValue_continuous z hz (fun t =>
      isUnit_of_norm_sub_one_lt _ ((hgram t).1.trans_le hτ1))
  have hz1 : z 1 = 1 := by
    simp only [z, finiteRohlinSum, hv1, OneMemClass.coe_one, one_mul, hes]
  have hw1 : w 1 = 1 := by
    apply Subtype.ext
    change clockPolarValue (z 1) = 1
    rw [hz1, clockPolarValue_of_unitary 1 (one_mem _)]
  refine ⟨w 0, ?_, (hp 0).2⟩
  let p : Path (w 0) 1 :=
    { toFun := w, continuous_toFun := hw, source' := rfl, target' := hw1 }
  exact ⟨p.symm⟩

/-- The mesh estimate keeps the additive modulus error. -/
lemma finiteCocycleCoefficient_clock_step (α : unitary E →* unitary E) (w : unitary E)
    (hα : ∀ u v : unitary E, ‖(α u : E) - α v‖ ≤ ‖(u : E) - v‖)
    {N : ℕ} (p : Path (finiteGroupCocycle α w N) 1)
    (L ρ : ℝ) (hp : ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b| + ρ)
    (k : ℕ) (a b : unitInterval) :
    ‖(w : E) * α (finiteCocycleCoefficient α w p k a) -
      finiteCocycleCoefficient α w p (k + 1) b‖ ≤ L * |(a : ℝ) - b| + ρ := by
  change ‖(↑(w * α (finiteCocycleCoefficient α w p k a)) : E) -
    (finiteCocycleCoefficient α w p (k + 1) b : E)‖ ≤ _
  rw [finiteCocycleCoefficient_step]
  change ‖(↑(finiteGroupCocycle α w (k + 1)) : E) * ((α^[k + 1]) (p a) : E) -
    (↑(finiteGroupCocycle α w (k + 1)) : E) * ((α^[k + 1]) (p b) : E)‖ ≤ _
  rw [← mul_sub, CStarRing.norm_coe_unitary_mul]
  exact (unitaryHom_iterate_sub_norm_le α hα (k + 1) (p a) (p b)).trans (hp a b)

def clockGridPoint (N : ℕ) (hN : 0 < N) (k : ZMod N) : unitInterval :=
  cocycleGridTime N hN ⟨k.val, by
    let : NeZero N := ⟨hN.ne'⟩
    have := ZMod.val_lt k
    omega⟩

def clockPeriodicCoefficient (α : unitary E →* unitary E) (w : unitary E)
    {N : ℕ} (hN : 0 < N) (p : Path (finiteGroupCocycle α w N) 1)
    (k : ZMod N) : unitary E :=
  finiteCocycleCoefficient α w p k.val (clockGridPoint N hN k)

lemma clockPeriodicCoefficient_zero (α : unitary E →* unitary E) (w : unitary E)
    {N : ℕ} (hN : 0 < N) (p : Path (finiteGroupCocycle α w N) 1) :
    clockPeriodicCoefficient α w hN p 0 = finiteGroupCocycle α w N := by
  have ht : clockGridPoint N hN 0 = 0 := by
    apply Subtype.ext
    change (ZMod.val (0 : ZMod N) : ℝ) / N = (0 : unitInterval)
    simp only [ZMod.val_zero, Nat.cast_zero, zero_div, Set.Icc.coe_zero]
  simp only [clockPeriodicCoefficient, ZMod.val_zero, ht, finiteCocycleCoefficient_zero]

/-- The last-to-first transition uses the exact endpoint equality, including
the height-one case. -/
lemma clockPeriodicCoefficient_step (α : unitary E →* unitary E) (w : unitary E)
    (hα : ∀ u v : unitary E, ‖(α u : E) - α v‖ ≤ ‖(u : E) - v‖)
    {N : ℕ} (hN : 0 < N) (p : Path (finiteGroupCocycle α w N) 1)
    (L ρ : ℝ) (hp : ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b| + ρ)
    (k : ZMod N) :
    ‖(w : E) * α (clockPeriodicCoefficient α w hN p k) -
      clockPeriodicCoefficient α w hN p (k + 1)‖ ≤ L / N + ρ := by
  let : NeZero N := ⟨hN.ne'⟩
  let i : Fin N := ⟨k.val, ZMod.val_lt k⟩
  have ha : clockGridPoint N hN k = cocycleGridTime N hN i.castSucc := by rfl
  have hb : finiteCocycleCoefficient α w p (k.val + 1)
      (cocycleGridTime N hN i.succ) = clockPeriodicCoefficient α w hN p (k + 1) := by
    have hcast : k + 1 = ((k.val + 1 : ℕ) : ZMod N) := by
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    have hval : (k + 1).val = (k.val + 1) % N := by rw [hcast, ZMod.val_natCast]
    by_cases hlt : k.val + 1 < N
    · have hval' : (k + 1).val = k.val + 1 := hval.trans (Nat.mod_eq_of_lt hlt)
      unfold clockPeriodicCoefficient
      rw [hval']
      congr 1
      apply Subtype.ext
      change ((k.val + 1 : ℕ) : ℝ) / N = ((k + 1).val : ℝ) / N
      rw [hval']
    · have hend : k.val + 1 = N := by have := ZMod.val_lt k; omega
      have hz : k + 1 = 0 := by rw [hcast, hend]; exact ZMod.natCast_self N
      have ht : cocycleGridTime N hN i.succ = 1 := by
        apply Subtype.ext
        change ((k.val + 1 : ℕ) : ℝ) / N = 1
        rw [hend]
        exact div_self (by exact_mod_cast hN.ne')
      rw [ht, hend, finiteCocycleCoefficient_terminal, hz,
        clockPeriodicCoefficient_zero]
  have h := finiteCocycleCoefficient_clock_step α w hα p L ρ hp k.val
    (cocycleGridTime N hN i.castSucc) (cocycleGridTime N hN i.succ)
  rw [cocycleGridTime_step] at h
  rw [← ha, hb, mul_one_div] at h
  exact h

/-- All paths on the same partition give a connected approximate
coboundary. The finite tolerance can be chosen after the height. -/
lemma connected_rohlin_cocycle_of_family [Nontrivial E]
    {N : ℕ} [NeZero N] (hN : 0 < N) (φ : E →⋆ₙₐ[ℂ] E)
    (α : unitary E →* unitary E) (hco : ∀ u, (α u : E) = φ u)
    (hcont : Continuous α)
    (hα : ∀ u v : unitary E, ‖(α u : E) - α v‖ ≤ ‖(u : E) - v‖)
    (w : unitary E) (e : ZMod N → E)
    (he : ∀ k, IsStarProjection (e k))
    (heo : ∀ k l, k ≠ l → e k * e l = 0)
    (L ρ C η ε δ : ℝ) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hs : ∀ k, ‖φ (e k) - e (k + 1)‖ ≤ η)
    (r : ∀ n : ℕ, n ≤ N → Path (finiteGroupCocycle α w n) 1)
    (hr : ∀ n hn, ClockPathControl (r n hn) e L ρ C)
    (hsmall : 2 * C + 2 * N * η ≤ δ)
    (hpolar : ∀ (v : ZMod N → unitInterval → unitary E),
      (∀ i, Continuous (v i)) → (∀ i, v i 1 = 1) →
      (∀ t i, ‖(v i t : E) * e i - e i * (v i t : E)‖ ≤ δ) →
      ∃ u : unitary E, Joined (1 : unitary E) u ∧
        ‖(u : E) - finiteRohlinSum (fun i => v i 0) e‖ < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      ‖(w : E) * φ u - u‖ ≤ 2 * ε + Real.sqrt N * (L / N + ρ) + N * η := by
  let q := r N le_rfl
  let c := clockPeriodicCoefficient α w hN q
  let v (k : ZMod N) : Path (c k) 1 :=
    (clockCoefficientContraction α hcont (r k.val (Nat.le_of_lt (ZMod.val_lt k))) q
      (clockGridPoint N hN k) k.val).cast rfl rfl
  have hvc (t : unitInterval) (k : ZMod N) :
      ‖(v k t : E) * e k - e k * (v k t : E)‖ ≤ δ := by
    have h := clockCoefficientContraction_commutator φ α hco hcont e η C hs
      (r k.val (Nat.le_of_lt (ZMod.val_lt k))) q
      (hr _ _).commutator (hr N le_rfl).commutator (clockGridPoint N hN k) t k.val k
    have hη : 0 ≤ η := (norm_nonneg _).trans (hs k)
    exact h.trans ((by
      have hn : (k.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt (ZMod.val_lt k))
      nlinarith : 2 * C + 2 * k.val * η ≤ 2 * C + 2 * N * η).trans hsmall)
  obtain ⟨u, hu, hnear⟩ := hpolar (fun k t => v k t) (fun k => (v k).continuous)
    (fun k => (v k).target) hvc
  have hz : finiteRohlinSum (fun k => v k 0) e = finiteRohlinSum c e := by
    simp only [Path.source]
  rw [hz] at hnear
  let z := finiteRohlinSum c e
  have hres : ‖(w : E) * φ z - z‖ ≤ Real.sqrt N * (L / N + ρ) + N * η := by
    have hb := finiteRohlinSum_defect_le φ w (Equiv.addRight (1 : ZMod N)) c e
      (fun k => (he k).isSelfAdjoint.star_eq) (fun k => (he k).isIdempotentElem.eq)
      heo (L / N + ρ) η (by positivity)
      (fun k => by
        rw [← hco]
        exact clockPeriodicCoefficient_step α w hα hN q L ρ (hr N le_rfl).modulus k)
      hs
    simpa only [ZMod.card] using hb
  refine ⟨u, hu, ?_⟩
  calc
    _ ≤ ‖(w : E) * φ u - (w : E) * φ z‖ + ‖(w : E) * φ z - z‖ + ‖z - u‖ := by
      have h1 := norm_sub_le_norm_sub_add_norm_sub ((w : E) * φ u) ((w : E) * φ z) z
      have h2 := norm_sub_le_norm_sub_add_norm_sub ((w : E) * φ u) z (u : E)
      linarith
    _ = ‖φ (u : E) - φ z‖ + ‖(w : E) * φ z - z‖ + ‖z - u‖ := by
      rw [← mul_sub, CStarRing.norm_coe_unitary_mul]
    _ ≤ ‖(u : E) - z‖ + (Real.sqrt N * (L / N + ρ) + N * η) + ‖z - u‖ := by
      exact add_le_add (add_le_add
        (by rw [← map_sub]; exact NonUnitalStarAlgHom.norm_apply_le φ _) hres) le_rfl
    _ ≤ _ := by rw [norm_sub_rev z]; linarith

/-- All partition, path, and Gram hypotheses are discharged for the actual
commuting full binary rows. Only the displayed mesh term remains. -/
lemma exists_joint_connected_coboundary_at_height [Nontrivial E]
    (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      ‖(binaryRowUnitary s t hs ht hsum htsum : E) * finiteRowShift s u - u‖ ≤
        (320 * Real.pi) * Real.sqrt (2 ^ m : ℕ) / (2 ^ m : ℕ) + ε := by
  classical
  let N := 2 ^ m
  have hN : 0 < N := by dsimp only [N]; positivity
  let : NeZero N := ⟨hN.ne'⟩
  let φ := finiteCuntzDiagonalHom s hs
  let α := binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
    (by simpa using hs 1 1) (by simpa using hs 0 1)
  let w := binaryRowUnitary s t hs ht hsum htsum
  have hco (u : unitary E) : (α u : E) = φ u := binarySplitHom_coe s hs hsum u
  have hcont : Continuous α := by
    exact (binaryCornerUnitary_continuous (s 0) (by simpa using hs 0 0)).mul
      (binaryCornerUnitary_continuous (s 1) (by simpa using hs 1 1))
  have hα (u v : unitary E) : ‖(α u : E) - α v‖ ≤ ‖(u : E) - v‖ :=
    binarySplitHom_sub_norm_le s hs hsum u v
  obtain ⟨δ, hδ, hp⟩ := exists_connected_rohlin_polar_tolerance (E := E)
    (I := ZMod N) (ε / 4) (by positivity)
  let D : ℝ := Real.sqrt N + N + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  let η := min (δ / (4 * ((N : ℝ) + 1))) (ε / (4 * D))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hsmall : 2 * η + 2 * N * η ≤ δ := by
    have hl : η ≤ δ / (4 * ((N : ℝ) + 1)) := min_le_left _ _
    have hb := (le_div_iff₀ (show 0 < 4 * ((N : ℝ) + 1) by positivity)).mp hl
    nlinarith
  have herr : (Real.sqrt N + N) * η ≤ ε / 4 := by
    have hl : η ≤ ε / (4 * D) := min_le_right _ _
    have hb := (le_div_iff₀ (show 0 < 4 * D by positivity)).mp hl
    dsimp only [D] at hb
    nlinarith [hη.le]
  obtain ⟨e, he, hes, heo, hS, _hT, hpaths⟩ :=
    exists_joint_clocked_cocycle_family s t hs ht hsum htsum hcomm m N η hη
  choose r hr using hpaths
  obtain ⟨u, hu, hb⟩ := connected_rohlin_cocycle_of_family hN φ α hco hcont hα w e
    he heo (320 * Real.pi) η η η (ε / 4) δ (by positivity) hη.le
    (fun k => (hS k).le) r hr hsmall (hp e he hes heo)
  refine ⟨u, hu, hb.trans ?_⟩
  calc
    2 * (ε / 4) + Real.sqrt N * (320 * Real.pi / N + η) + N * η =
        (320 * Real.pi) * Real.sqrt N / N + 2 * (ε / 4) +
          (Real.sqrt N + N) * η := by ring
    _ ≤ (320 * Real.pi) * Real.sqrt N / N + ε := by linarith

/-- The finite-height mesh term tends to zero, with every other tolerance
chosen only after the height. This is a genuine connected conjugacy result
for two commuting full binary Cuntz rows. -/
lemma exists_connected_binary_row_conjugacy [Nontrivial E]
    (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      ∀ i, ‖(u : E) * s i * star (u : E) - t i‖ < ε := by
  let L := 320 * Real.pi
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 * L / ε) (show (1 : ℝ) < 2 by norm_num)
  have ha : 0 < (2 : ℝ) ^ k := by positivity
  have hpow : ((2 ^ (2 * k) : ℕ) : ℝ) = ((2 : ℝ) ^ k) ^ 2 := by
    push_cast
    rw [Nat.mul_comm 2 k, pow_mul]
  have hsqrt : Real.sqrt ((2 ^ (2 * k) : ℕ) : ℝ) = (2 : ℝ) ^ k := by
    rw [hpow, Real.sqrt_sq ha.le]
  have hratio : L * Real.sqrt ((2 ^ (2 * k) : ℕ) : ℝ) /
      ((2 ^ (2 * k) : ℕ) : ℝ) < ε / 4 := by
    rw [hsqrt, hpow]
    have hid : L * (2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ 2 = L / (2 : ℝ) ^ k := by
      field_simp
    rw [hid]
    apply (div_lt_iff₀ ha).mpr
    have hh := (div_lt_iff₀ hε).mp hk
    nlinarith
  obtain ⟨u, hu, hb⟩ := exists_joint_connected_coboundary_at_height s t hs ht hsum htsum
    hcomm (2 * k) (ε / 2) (half_pos hε)
  have herr : ‖(binaryRowUnitary s t hs ht hsum htsum : E) * finiteRowShift s u - u‖ < ε := by
    apply hb.trans_lt
    change L * Real.sqrt ((2 ^ (2 * k) : ℕ) : ℝ) /
      ((2 ^ (2 * k) : ℕ) : ℝ) + ε / 2 < ε
    linarith
  have hinter (i : Fin 2) : ‖(u : E) * s i - t i * (u : E)‖ < ε := by
    have hid : t i * (u : E) - (u : E) * s i =
        ((binaryRowUnitary s t hs ht hsum htsum : E) * finiteRowShift s u - u) * s i := by
      rw [sub_mul, mul_assoc, finiteRowShift_mul_row 1 s hs (u : E) (mul_one _) i,
        ← mul_assoc]
      change t i * (u : E) - (u : E) * s i =
        (finiteRowCocycle s t * s i) * (u : E) - (u : E) * s i
      rw [finiteRowCocycle_mul_row 1 s t (star_one _) (one_mul _) hs ht]
    have hsi : ‖s i‖ ≤ 1 := by
      have hh := congrArg norm (show star (s i) * s i = 1 by simpa using hs i i)
      rw [CStarRing.norm_star_mul_self, norm_one] at hh
      nlinarith [norm_nonneg (s i)]
    rw [norm_sub_rev, hid]
    exact (norm_mul_le _ _).trans_lt
      ((mul_le_mul_of_nonneg_left hsi (norm_nonneg _)).trans_lt (by simpa using herr))
  refine ⟨u, hu, fun i => ?_⟩
  calc
    _ = ‖((u : E) * s i - t i * (u : E)) * (star u : unitary E)‖ := by
      congr 1
      change (u : E) * s i * star (u : E) - t i =
        ((u : E) * s i - t i * (u : E)) * star (u : E)
      rw [sub_mul, mul_assoc (t i), u.property.2, mul_one]
    _ = ‖(u : E) * s i - t i * (u : E)‖ := CStarRing.norm_mul_coe_unitary _ _
    _ < ε := hinter i

end WeakPureInfiniteness

end

end OAI
