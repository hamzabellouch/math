import Mathlib
import OAI.Computability.DirectedFeedback.Probability.DescentProbability

namespace OAI

namespace DFVSGames.Gadget.Enlargement

open scoped BigOperators Classical

noncomputable section

def probability {Ω : Type*} [Fintype Ω] (p : Ω → Prop) : ℚ :=
  (Nat.card {x : Ω // p x} : ℚ) / (Nat.card Ω : ℚ)

theorem probability_exists_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : I → Ω → Prop) :
    probability (fun x => ∃ i, p i x) ≤ ∑ i, probability (p i) := by
  classical
  have heq : (Finset.univ.filter fun x => ∃ i, p i x) =
      Finset.univ.biUnion (fun i => Finset.univ.filter (p i)) := by
    ext x
    simp
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [heq, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset I))
    (t := fun i => Finset.univ.filter (p i)))

theorem probability_preimage_of_fibers {Ω T : Type*} [Fintype Ω] [Fintype T]
    [Nonempty Ω] [Nonempty T] (f : Ω → T)
    (hf : ∀ x y : T, Nat.card {a : Ω // f a = x} = Nat.card {a : Ω // f a = y})
    (p : T → Prop) : probability (fun a => p (f a)) = probability p := by
  classical
  let t₀ : T := Classical.choice inferInstance
  let c := (Finset.univ.filter fun a => f a = t₀).card
  have hfc (x : T) : (Finset.univ.filter fun a => f a = x).card = c := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hf x t₀
  have hΩ : Fintype.card Ω = Fintype.card T * c := by
    calc
      Fintype.card Ω = ∑ t : T, (Finset.univ.filter fun a => f a = t).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = Fintype.card T * c := by simp_rw [hfc]; simp
  have hp : (Finset.univ.filter fun a => p (f a)).card =
      (Finset.univ.filter p).card * c := by
    calc
      _ = ∑ t ∈ Finset.univ.filter p,
          (Finset.univ.filter fun a => f a = t).card := by
        symm
        simpa using Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset Ω) (Finset.univ.filter p) f
      _ = _ := by simp_rw [hfc]; simp
  have hc : (c : ℚ) ≠ 0 := by
    have : c ≠ 0 := by
      intro hc
      have := Fintype.card_pos (α := Ω)
      simp [hc] at hΩ
    exact_mod_cast this
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hp, hΩ]
  push_cast
  exact mul_div_mul_right _ _ hc

theorem exists_equiv_map_nonzero {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : V ≃ₗ[F] V, e x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton F V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton F V y hy
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e, ?_⟩
  have h := (he (ex 1)).symm
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h

abbrev LinearInjection (F B K : Type*) [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K] :=
  {L : B →ₗ[F] K // Function.Injective L}

theorem linearInjection_nonempty_of_finrank_le {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (h : Module.finrank F B ≤ Module.finrank F K) :
    Nonempty (LinearInjection F B K) := by
  obtain ⟨L, hL⟩ := finrank_le_iff_exists_linearMap.mp h
  exact ⟨⟨L, hL⟩⟩

def postcompose {F B K : Type*} [Field F] [AddCommGroup B] [Module F B]
    [AddCommGroup K] [Module F K] (e : K ≃ₗ[F] K) :
    LinearInjection F B K ≃ LinearInjection F B K where
  toFun L := ⟨e.toLinearMap.comp L.1, e.injective.comp L.2⟩
  invFun L := ⟨e.symm.toLinearMap.comp L.1, e.symm.injective.comp L.2⟩
  left_inv L := by
    apply Subtype.ext
    ext x
    exact e.symm_apply_apply (L.1 x)
  right_inv L := by
    apply Subtype.ext
    ext x
    exact e.apply_symm_apply (L.1 x)

theorem injection_eval_ne_zero {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K]
    (L : LinearInjection F B K) {b : B} (hb : b ≠ 0) : L.1 b ≠ 0 := by
  intro h
  apply hb
  apply L.2
  simpa using h

theorem exists_injection_hitting_nonzero {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (h : Module.finrank F B ≤ Module.finrank F K)
    (b : B) (hb : b ≠ 0) (x : K) (hx : x ≠ 0) :
    ∃ L : LinearInjection F B K, L.1 b = x := by
  obtain ⟨L⟩ := linearInjection_nonempty_of_finrank_le h
  obtain ⟨e, he⟩ := exists_equiv_map_nonzero (F := F) (L.1 b) x
    (injection_eval_ne_zero L hb) hx
  exact ⟨postcompose e L, he⟩

def productShift {F B K : Type*} [Field F] [AddCommGroup B] [Module F B]
    [AddCommGroup K] [Module F K] [Fintype (LinearInjection F B K)] :
    (LinearInjection F B K → B) →ₗ[F] K where
  toFun b := ∑ L : LinearInjection F B K, L.1 (b L)
  map_add' b c := by simp [map_add, Finset.sum_add_distrib]
  map_smul' t b := by simp [map_smul, Finset.smul_sum]

theorem productShift_surjective {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    [Fintype (LinearInjection F B K)]
    (h : Module.finrank F B ≤ Module.finrank F K)
    (b : B) (hb : b ≠ 0) :
    Function.Surjective (productShift (F := F) (B := B) (K := K)) := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact ⟨0, map_zero _⟩
  · obtain ⟨L, hL⟩ := exists_injection_hitting_nonzero h b hb x hx
    refine ⟨fun L' => if L' = L then b else 0, ?_⟩
    simpa [productShift, apply_ite] using hL

def enlargedOutput {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) : K := ∑ L : LinearInjection F B K, L.1 (C (x L))

theorem enlargedOutput_shift {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Module F V] [Fintype (LinearInjection F B K)]
    (C : V → B) (i : B →ₗ[F] V)
    (hC : ∀ x b, C (x + i b) = C x + b)
    (x : LinearInjection F B K → V) (b : LinearInjection F B K → B) :
    enlargedOutput C (fun L => x L + i (b L)) =
      enlargedOutput C x + productShift b := by
  simp [enlargedOutput, productShift, hC, map_add, Finset.sum_add_distrib]

theorem enlargedOutput_update {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) (L : LinearInjection F B K) (y : V) :
    enlargedOutput C (Function.update x L y) =
      enlargedOutput C x + L.1 (C y - C (x L)) := by
  classical
  have hfun : (fun J => J.1 (C (Function.update x L y J))) =
      Function.update (fun J : LinearInjection F B K => J.1 (C (x J))) L (L.1 (C y)) := by
    funext J
    by_cases h : J = L
    · subst J
      simp
    · simp [h]
  unfold enlargedOutput
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ L)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ L)]
  rw [map_sub]
  abel

theorem enlargedOutput_update_ne_iff {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) (L : LinearInjection F B K) (y : V) :
    enlargedOutput C (Function.update x L y) ≠ enlargedOutput C x ↔ C y ≠ C (x L) := by
  rw [enlargedOutput_update, ne_eq, add_eq_left, map_eq_zero_iff _ L.2,
    sub_eq_zero, ne_eq]

theorem injection_eval_uniform {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K]
    [Fintype K] [Fintype (LinearInjection F B K)]
    [Nonempty (LinearInjection F B K)] (b : B) (hb : b ≠ 0)
    (p : {x : K // x ≠ 0} → Prop) :
    probability (fun L : LinearInjection F B K =>
      p ⟨L.1 b, injection_eval_ne_zero L hb⟩) = probability p := by
  classical
  let : Nonempty {x : K // x ≠ 0} :=
    ⟨⟨(Classical.choice inferInstance : LinearInjection F B K).1 b,
      injection_eval_ne_zero _ hb⟩⟩
  let f : LinearInjection F B K → {x : K // x ≠ 0} :=
    fun L => ⟨L.1 b, injection_eval_ne_zero L hb⟩
  apply probability_preimage_of_fibers f
  intro x y
  obtain ⟨e, he⟩ := exists_equiv_map_nonzero (F := F) x.1 y.1 x.2 y.2
  let ee : {L : LinearInjection F B K // f L = x} ≃
      {L : LinearInjection F B K // f L = y} :=
    (postcompose e).subtypeEquiv (fun L => by
      change f L = x ↔ f (postcompose e L) = y
      constructor
      · intro h
        apply Subtype.ext
        change e (L.1 b) = y.1
        rw [show L.1 b = x.1 from congrArg Subtype.val h, he]
      · intro h
        apply Subtype.ext
        apply e.injective
        exact (congrArg Subtype.val h).trans he.symm)
  exact Nat.card_congr ee

theorem pullback_ne_top_iff {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [FiniteDimensional F B] [AddCommGroup K] [Module F K]
    (L : B →ₗ[F] K) (S : Submodule F (Module.Dual F K)) :
    S.map L.dualMap ≠ ⊤ ↔ ∃ b : B, b ≠ 0 ∧ L b ∈ S.dualCoannihilator := by
  let W := S.map L.dualMap
  have hann : W.dualCoannihilator = S.dualCoannihilator.comap L := by
    ext b
    simp only [Submodule.mem_dualCoannihilator, Submodule.mem_comap,
      ]
    constructor
    · intro h z hz
      exact h (z.comp L) ⟨z, hz, rfl⟩
    · intro h z ⟨w, hw, hwz⟩
      subst z
      exact h w hw
  constructor
  · intro hW
    have hn : W.dualCoannihilator ≠ ⊥ := by
      intro hz
      have hh := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
      rw [hz, Submodule.dualAnnihilator_bot] at hh
      exact hW hh.symm
    obtain ⟨b, hb, hb0⟩ := (Submodule.ne_bot_iff _).1 hn
    exact ⟨b, hb0, by simpa [hann] using hb⟩
  · rintro ⟨b, hb0, hb⟩ htop
    have hz : b ∈ W.dualCoannihilator := by simpa [hann] using hb
    change b ∈ (S.map L.dualMap).dualCoannihilator at hz
    rw [htop] at hz
    have hall : ∀ z : Module.Dual F B, z b = 0 := by
      simpa only [Submodule.mem_dualCoannihilator, Submodule.mem_top,
        forall_true_left] using hz
    obtain ⟨z, hz'⟩ := Module.Projective.exists_dual_ne_zero F hb0
    exact hz' (hall z)

theorem nonzero_density_le (d r : ℕ) (h : 0 < d + r) :
    ((2 : ℚ) ^ d - 1) / ((2 : ℚ) ^ (d + r) - 1) ≤ 1 / (2 : ℚ) ^ r := by
  have hpow : 1 < (2 : ℚ) ^ (d + r) := one_lt_pow₀ (by norm_num) (by omega)
  have hr : (1 : ℚ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  rw [pow_add]
  nlinarith

theorem card_nonzero_binary (K : Type*) [AddCommGroup K] [Module (ZMod 2) K]
    [Fintype K] :
    Nat.card {x : K // x ≠ 0} = 2 ^ Module.finrank (ZMod 2) K - 1 := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : K => x = 0), Fintype.card_subtype_eq]
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

theorem probability_nonzero_subspace (K : Type*) [AddCommGroup K]
    [Module (ZMod 2) K] [Fintype K] (W : Submodule (ZMod 2) K) :
    probability (fun x : {x : K // x ≠ 0} => x.1 ∈ W) =
      ((2 : ℚ) ^ Module.finrank (ZMod 2) W - 1) /
        ((2 : ℚ) ^ Module.finrank (ZMod 2) K - 1) := by
  classical
  let : Fintype W := Fintype.ofFinite _
  let e : {x : {x : K // x ≠ 0} // x.1 ∈ W} ≃ {x : W // x ≠ 0} :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, by
        intro h
        exact x.1.2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨⟨x.1.1, by
        intro h
        apply x.2
        exact Subtype.ext h⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold probability
  rw [Nat.card_congr e,
    card_nonzero_binary W, card_nonzero_binary K]
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)),
    Nat.cast_sub (Nat.one_le_pow _ _ (by decide))]
  push_cast ; rfl

theorem probability_annihilator_le (K : Type*) [AddCommGroup K]
    [Module (ZMod 2) K] [Fintype K] [FiniteDimensional (ZMod 2) K]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hK : 0 < Module.finrank (ZMod 2) K) :
    probability (fun x : {x : K // x ≠ 0} => x.1 ∈ S.dualCoannihilator) ≤
      1 / (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
  rw [probability_nonzero_subspace]
  have hr := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  rw [← hr, add_comm (Module.finrank (ZMod 2) S)]
  apply nonzero_density_le
  omega

theorem union_bound_le_quarter (b r : ℕ) (hr : b + 2 ≤ r) :
    ((2 : ℚ) ^ b - 1) / (2 : ℚ) ^ r ≤ 1 / 4 := by
  have hpow : (2 : ℚ) ^ (b + 2) ≤ (2 : ℚ) ^ r :=
    pow_le_pow_right₀ (by norm_num) hr
  rw [pow_add] at hpow
  norm_num at hpow
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ r)).2
  nlinarith [show (0 : ℚ) ≤ 2 ^ b by positivity]

theorem pullback_failure_probability_le {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hK : 0 < Module.finrank (ZMod 2) K) :
    probability (fun L : LinearInjection (ZMod 2) B K => S.map L.1.dualMap ≠ ⊤) ≤
      ((2 : ℚ) ^ Module.finrank (ZMod 2) B - 1) /
        (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
  classical
  calc
    _ = probability (fun L : LinearInjection (ZMod 2) B K =>
        ∃ b : {b : B // b ≠ 0}, L.1 b.1 ∈ S.dualCoannihilator) := by
      congr 1
      funext L
      apply propext
      rw [pullback_ne_top_iff]
      exact ⟨fun ⟨b, hb, h⟩ => ⟨⟨b, hb⟩, h⟩,
        fun ⟨b, h⟩ => ⟨b.1, b.2, h⟩⟩
    _ ≤ ∑ b : {b : B // b ≠ 0}, probability
        (fun L : LinearInjection (ZMod 2) B K => L.1 b.1 ∈ S.dualCoannihilator) :=
      probability_exists_le_sum _
    _ ≤ ∑ _b : {b : B // b ≠ 0},
        1 / (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
      apply Finset.sum_le_sum
      intro b _
      rw [injection_eval_uniform b.1 b.2
        (fun x : {x : K // x ≠ 0} => x.1 ∈ S.dualCoannihilator)]
      exact probability_annihilator_le K S hK
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, card_nonzero_binary B,
        Nat.cast_sub (Nat.one_le_pow _ _ (by decide))]
      push_cast
      ring

theorem pullback_failure_probability_le_quarter {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2) S) :
    probability (fun L : LinearInjection (ZMod 2) B K => S.map L.1.dualMap ≠ ⊤) ≤
      1 / 4 := by
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  exact (pullback_failure_probability_le S (by omega)).trans
    (union_bound_le_quarter _ _ hr)

theorem probability_not {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → Prop) : probability (fun x => ¬ p x) = 1 - probability p := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω)) p
  have h' : ((Finset.univ.filter p).card : ℚ) +
      ((Finset.univ.filter fun x => ¬p x).card : ℚ) = Fintype.card Ω := by
    exact_mod_cast h
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply (eq_sub_iff_add_eq).2
  rw [← add_div, add_comm, h', div_self hcard]

theorem average_detection_lower_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (bad : Ω → Prop) (detected : Ω → ℚ)
    (hnonneg : ∀ x, 0 ≤ detected x)
    (hgood : ∀ x, ¬bad x → 1 / 4 ≤ detected x) :
    (1 - probability bad) * (1 / 4) ≤
      (∑ x, detected x) / (Fintype.card Ω : ℚ) := by
  classical
  have hs : ∑ x : Ω, (if bad x then (0 : ℚ) else 1 / 4) ≤ ∑ x, detected x := by
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : bad x
    · simpa [hx] using hnonneg x
    · simpa [hx] using hgood x hx
  have heq : ∑ x : Ω, (if bad x then (0 : ℚ) else 1 / 4) =
      ((Finset.univ.filter fun x => ¬bad x).card : ℚ) * (1 / 4) := by
    rw [Finset.sum_ite]
    simp
  rw [heq] at hs
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Fintype.card Ω) :
    (0 : ℚ) ≤ Fintype.card Ω)
  rw [← probability_not]
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [div_mul_eq_mul_div] using hd

theorem detection_constants {bad detected : ℚ} (hbad : bad ≤ 1 / 4)
    (hdetected : (1 - bad) * (1 / 4) ≤ detected) :
    3 / 16 ≤ detected ∧ 1 / 8 ≤ detected := by
  constructor <;> linarith

theorem enlarged_detection {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2) S)
    (detected : LinearInjection (ZMod 2) B K → ℚ)
    (hnonneg : ∀ L, 0 ≤ detected L)
    (hbase : ∀ L, S.map L.1.dualMap = ⊤ → 1 / 4 ≤ detected L) :
    3 / 16 ≤ (∑ L, detected L) / (Fintype.card (LinearInjection (ZMod 2) B K) : ℚ) ∧
    1 / 8 ≤ (∑ L, detected L) / (Fintype.card (LinearInjection (ZMod 2) B K) : ℚ) := by
  apply detection_constants (pullback_failure_probability_le_quarter S hr)
  apply average_detection_lower_bound _ detected hnonneg
  intro L hL
  exact hbase L (not_not.mp hL)

end

end DFVSGames.Gadget.Enlargement

noncomputable section

namespace DFVSGames.Gadget.EnlargementConstruction

open scoped BigOperators Classical
open Enlargement

theorem probability_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (p : Ξ → Prop) :
    probability (fun x : Ω => p (e x)) = probability p := by
  classical
  unfold probability
  rw [Nat.card_congr (Equiv.subtypeEquivOfSubtype (p := p) e), Nat.card_congr e]

theorem probability_eq_sum_indicator {Ω : Type*} [Fintype Ω]
    (p : Ω → Prop) :
    probability p =
      (∑ x : Ω, if p x then (1 : ℚ) else 0) / (Fintype.card Ω : ℚ) := by
  classical
  simp only [probability, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem probability_prod_average {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → Ξ → Prop) :
    probability (fun z : Ω × Ξ => p z.1 z.2) =
      (∑ x : Ω, probability (p x)) / (Fintype.card Ω : ℚ) := by
  classical
  simp_rw [probability_eq_sum_indicator]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.sum_div, div_div]
  congr 1
  exact mul_comm _ _

theorem probability_prod_average_right {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → Ξ → Prop) :
    probability (fun z : Ω × Ξ => p z.1 z.2) =
      (∑ y : Ξ, probability (fun x : Ω => p x y)) /
        (Fintype.card Ξ : ℚ) := by
  classical
  simp_rw [probability_eq_sum_indicator]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type_right,
    ← Finset.sum_div, div_div]

theorem probability_coordinate {I X : Type*} [Fintype I] [Fintype X]
    (i : I) (p : X → Prop) :
    probability (fun g : I → X => p (g i)) = probability p := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      let : IsEmpty X := hX
      let : IsEmpty (I → X) := ⟨fun g => isEmptyElim (g i)⟩
      simp [probability]
  | inr hX =>
      let : Nonempty X := hX
      let : Nonempty (I → X) := ⟨fun _ => Classical.choice hX⟩
      apply probability_preimage_of_fibers (fun g : I → X => g i)
      intro x y
      let e : (I → X) ≃ (I → X) :=
        Equiv.piCongrRight (fun _ : I => Equiv.swap x y)
      let ee : {g : I → X // g i = x} ≃
          {g : I → X // g i = y} :=
        e.subtypeEquiv (fun g => by
          change g i = x ↔ Equiv.swap x y (g i) = y
          constructor
          · intro h
            rw [h, Equiv.swap_apply_left]
          · intro h
            apply (Equiv.swap x y).injective
            exact h.trans (Equiv.swap_apply_left x y).symm)
      exact Nat.card_congr ee

theorem probability_coordinate_prod {I X N : Type*}
    [Fintype I] [Fintype X] [Fintype N] (i : I) (p : X → N → Prop) :
    probability (fun z : (I → X) × N => p (z.1 i) z.2) =
      probability (fun z : X × N => p z.1 z.2) := by
  rw [probability_prod_average_right (fun (g : I → X) n => p (g i) n),
    probability_prod_average_right p]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact probability_coordinate i (fun x => p x n)

theorem probability_prod_reorder {Ω I N : Type*}
    [Fintype Ω] [Fintype I] [Fintype N] (p : Ω → I → N → Prop) :
    probability (fun z : Ω × (I × N) => p z.1 z.2.1 z.2.2) =
      probability (fun z : I × (Ω × N) => p z.2.1 z.1 z.2.2) := by
  let e : (Ω × (I × N)) ≃ (I × (Ω × N)) :=
    { toFun := fun z => (z.2.1, z.1, z.2.2)
      invFun := fun z => (z.2.1, z.1, z.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact probability_equiv e (fun z => p z.2.1 z.1 z.2.2)

theorem probability_prod_eq_of_const {Ω Ξ : Type*}
    [Fintype Ω] [Fintype Ξ] [Nonempty Ω]
    (p : Ω → Ξ → Prop) (q : ℚ) (h : ∀ x, probability (p x) = q) :
    probability (fun z : Ω × Ξ => p z.1 z.2) = q := by
  rw [probability_prod_average]
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ q hcard

theorem enlarged_single_copy_probability {F B K V N : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Fintype V] [Fintype N]
    [Fintype (LinearInjection F B K)]
    (C : V → B) (a : N → V) (L : LinearInjection F B K) :
    probability (fun z : (LinearInjection F B K → V) × N =>
      enlargedOutput C (Function.update z.1 L (z.1 L + a z.2)) ≠
        enlargedOutput C z.1) =
      probability (fun z : V × N => C (z.1 + a z.2) ≠ C z.1) := by
  calc
    _ = probability (fun z : (LinearInjection F B K → V) × N =>
        C (z.1 L + a z.2) ≠ C (z.1 L)) := by
      congr 1
      funext z
      exact propext (enlargedOutput_update_ne_iff C z.1 L (z.1 L + a z.2))
    _ = _ := probability_coordinate_prod L (fun x n => C (x + a n) ≠ C x)

theorem enlarged_random_copy_probability {F B K V N : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Fintype V] [Fintype N]
    [Fintype (LinearInjection F B K)] [Nonempty (LinearInjection F B K)]
    (C : V → B) (a : N → V) :
    probability (fun z : (LinearInjection F B K → V) ×
        (LinearInjection F B K × N) =>
      enlargedOutput C
        (Function.update z.1 z.2.1 (z.1 z.2.1 + a z.2.2)) ≠
          enlargedOutput C z.1) =
      probability (fun z : V × N => C (z.1 + a z.2) ≠ C z.1) := by
  rw [probability_prod_reorder (fun x L n =>
    enlargedOutput C (Function.update x L (x L + a n)) ≠ enlargedOutput C x)]
  apply probability_prod_eq_of_const (fun L (z : (LinearInjection F B K → V) × N) =>
    enlargedOutput C (Function.update z.1 L (z.1 L + a z.2)) ≠ enlargedOutput C z.1)
  intro L
  exact enlarged_single_copy_probability C a L

universe u

variable {B K V N : Type u}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

abbrev Copies (B K : Type u) [AddCommGroup B] [Module (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] := LinearInjection (ZMod 2) B K

@[instance_reducible]
noncomputable def copiesFintype : Fintype (Copies B K) :=
  Fintype.ofInjective (fun L : Copies B K => (L.1 : B → K)) (by
    intro L M h
    apply Subtype.ext
    exact LinearMap.ext (congrFun h))

local instance enlargementCopiesFintype : Fintype (Copies B K) := copiesFintype

def productEmbed (i : B →ₗ[ZMod 2] V) :
    (Copies B K → B) →ₗ[ZMod 2] (Copies B K → V) where
  toFun b L := i (b L)
  map_add' b c := by ext L; exact map_add i (b L) (c L)
  map_smul' t b := by ext L; exact map_smul i t (b L)

omit [Fintype B] [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] [Fintype V] in
theorem productEmbed_injective (i : B →ₗ[ZMod 2] V)
    (hi : Function.Injective i) : Function.Injective (productEmbed (K := K) i) := by
  intro b c h
  funext L
  apply hi
  exact congrFun h L

def productStage (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) : Stage (ZMod 2) K := by
  letI : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  exact
    { Input := Copies B K → V
      Shift := Copies B K → B
      Noise := Copies B K × N
      embed := productEmbed i
      embed_injective := productEmbed_injective i hi
      logical := productShift
      logical_surjective := productShift_surjective hdim b₀ hb₀
      output := enlargedOutput C
      equivariant := enlargedOutput_shift C i hC
      noise := fun t => Pi.single t.1 (noise t.2) }

def build (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) : Stage (ZMod 2) K :=
  StageQuotient.toStage (productStage i hi C hC noise hdim b₀ hb₀)

private theorem update_canonical {A B : Type*} (d : DecidableEq A) (f : A → B) (a : A) (b : B) :
    @Function.update A (fun _ => B) d f a b =
      @Function.update A (fun _ => B) (Classical.typeDecidableEq A) f a b := by
  cases Subsingleton.elim d (Classical.typeDecidableEq A : DecidableEq A)
  rfl

private theorem probability_pointwise {A : Type*} (i j : Fintype A) (p q : A → Prop)
    (h : ∀ a, p a ↔ q a) : @probability A i p = @probability A j q := by
  unfold probability
  have he : p = q := funext (fun a => propext (h a))
  rw [he]

omit [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] [Module (ZMod 2) V] [Fintype V] in
theorem add_single_eq_update (x : Copies B K → V) (L : Copies B K) (a : V) :
    x + Pi.single L a = Function.update x L (x L + a) := by
  funext J
  by_cases h : J = L
  · subst J
    simp
  · simp [h]

theorem change_iff (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) (x : Copies B K → V) (L : Copies B K) (n : N) :
    let s := productStage i hi C hC noise hdim b₀ hb₀
    StageQuotient.output s (StageQuotient.projection s x + StageQuotient.noise s (L, n)) ≠
        StageQuotient.output s (StageQuotient.projection s x) ↔
      C (x L + noise n) ≠ C (x L) := by
  dsimp only
  refine (StageQuotient.noise_change_iff
    (productStage i hi C hC noise hdim b₀ hb₀) x (L, n)).trans ?_
  change enlargedOutput C (x + Pi.single L (noise n)) ≠ enlargedOutput C x ↔ _
  rw [add_single_eq_update]
  have h := enlargedOutput_update_ne_iff C x L (x L + noise n)
  simp only [update_canonical] at h ⊢
  exact h

def copyObserver {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (L : Copies B K) : V →ₗ[ZMod 2] E :=
  T.comp ((StageQuotient.projection (productStage i hi C hC noise hdim b₀ hb₀)).comp
    (LinearMap.single (R := ZMod 2) (φ := fun _ : Copies B K => V) L))

theorem copyObserver_shift {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (L : Copies B K) :
    (copyObserver i hi C hC noise hdim b₀ hb₀ T L).comp i =
      (T.comp (StageQuotient.shift (productStage i hi C hC noise hdim b₀ hb₀))).comp L.1 := by
  ext b
  let s := productStage i hi C hC noise hdim b₀ hb₀
  have he : s.embed (Pi.single L b) = Pi.single L (i b) := by
    funext J
    change i ((Pi.single L b : Copies B K → B) J) =
      (Pi.single L (i b) : Copies B K → V) J
    by_cases h : J = L
    · subst J
      simp
    · simp [h]
  have hl : s.logical (Pi.single L b) = L.1 b := by
    change (∑ J : Copies B K, J.1 ((Pi.single L b : Copies B K → B) J)) = L.1 b
    simp [Pi.single_apply, apply_ite]
  have hh := congrArg T (StageQuotient.shift_logical s (Pi.single L b))
  rw [he, hl] at hh
  exact hh.symm

omit [Fintype B] [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] in
theorem dual_pullback_eq_top_iff {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (A : K →ₗ[ZMod 2] E) (L : B →ₗ[ZMod 2] K) :
    (LinearMap.range A.dualMap).map L.dualMap = ⊤ ↔ Function.Injective (A.comp L) := by
  rw [← LinearMap.range_comp, LinearMap.dualMap_comp_dualMap,
    LinearMap.range_eq_top, LinearMap.dualMap_surjective_iff]

theorem detection_average {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (hbase : ∀ U : V →ₗ[ZMod 2] E, Function.Injective (U.comp i) →
      1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0))
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (T.comp (StageQuotient.shift
        (productStage i hi C hC noise hdim b₀ hb₀))))) :
    1 / 8 ≤
      (∑ L : Copies B K, probability (fun n : N =>
        copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0)) /
          (Fintype.card (Copies B K) : ℚ) := by
  let : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  let A := T.comp (StageQuotient.shift (productStage i hi C hC noise hdim b₀ hb₀))
  apply (enlarged_detection (LinearMap.range A.dualMap)
    (by simpa only [LinearMap.finrank_range_dualMap_eq_finrank_range] using hr)
    (fun L => probability (fun n : N =>
      copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0))
    (fun _ => by unfold probability; positivity) ?_).2
  intro L hL
  apply hbase
  rw [copyObserver_shift]
  exact (dual_pullback_eq_top_iff A L.1).1 hL

omit [Fintype K] [FiniteDimensional (ZMod 2) K] in

theorem probability_projection (s : Stage (ZMod 2) K)
    [Fintype s.Input] [Fintype (StageQuotient.Space s)]
    (p : StageQuotient.Space s → Prop) :
    probability (fun x : s.Input => p (StageQuotient.projection s x)) = probability p := by
  apply probability_preimage_of_fibers (StageQuotient.projection s)
  intro x y
  have h := (Quotient.fiber_card (StageQuotient.shifts s) (StageQuotient.logical s) x).trans
    (Quotient.fiber_card (StageQuotient.shifts s) (StageQuotient.logical s) y).symm
  exact h

omit [Fintype K] [FiniteDimensional (ZMod 2) K] in
theorem probability_projection_prod (s : Stage (ZMod 2) K)
    [Fintype s.Input] [Fintype (StageQuotient.Space s)]
    {A : Type*} [Fintype A] (p : StageQuotient.Space s → A → Prop) :
    probability (fun z : s.Input × A => p (StageQuotient.projection s z.1) z.2) =
      probability (fun z : StageQuotient.Space s × A => p z.1 z.2) := by
  rw [probability_prod_average_right (fun x a => p (StageQuotient.projection s x) a),
    probability_prod_average_right p]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact probability_projection s (fun x => p x a)

theorem change_probability (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    [Fintype (StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀))] :
    let s := productStage i hi C hC noise hdim b₀ hb₀
    probability (fun z : StageQuotient.Space s × (Copies B K × N) =>
      StageQuotient.output s (z.1 + StageQuotient.noise s z.2) ≠ StageQuotient.output s z.1) =
        probability (fun z : V × N => C (z.1 + noise z.2) ≠ C z.1) := by
  dsimp only
  let : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  let s := productStage i hi C hC noise hdim b₀ hb₀
  let : Fintype s.Input := Fintype.ofFinite _
  have hp := probability_projection_prod s (fun q (t : Copies B K × N) =>
    StageQuotient.output s (q + StageQuotient.noise s t) ≠ StageQuotient.output s q)
  calc
    _ = probability (fun z : s.Input × (Copies B K × N) =>
        StageQuotient.output s (StageQuotient.projection s z.1 + StageQuotient.noise s z.2) ≠
          StageQuotient.output s (StageQuotient.projection s z.1)) := hp.symm
    _ = probability (fun z : (Copies B K → V) × (Copies B K × N) =>
        enlargedOutput C
          (Function.update z.1 z.2.1 (z.1 z.2.1 + noise z.2.2)) ≠ enlargedOutput C z.1) := by
      apply probability_pointwise
      intro z
      have h₁ := change_iff i hi C hC noise hdim b₀ hb₀ z.1 z.2.1 z.2.2
      have h₂ := enlargedOutput_update_ne_iff C z.1 z.2.1 (z.1 z.2.1 + noise z.2.2)
      simp only [update_canonical] at h₁ h₂ ⊢
      have hc := h₁.trans h₂.symm

      erw [update_canonical] at hc
      exact hc
    _ = _ := by
      have hh := enlarged_random_copy_probability (F := ZMod 2) (K := K) C noise
      simp only [update_canonical] at hh ⊢
      unfold probability at hh ⊢
      exact hh

theorem detection_probability {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (hbase : ∀ U : V →ₗ[ZMod 2] E, Function.Injective (U.comp i) →
      1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0))
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (T.comp (StageQuotient.shift
        (productStage i hi C hC noise hdim b₀ hb₀))))) :
    1 / 8 ≤ probability (fun t : Copies B K × N =>
      T (StageQuotient.noise (productStage i hi C hC noise hdim b₀ hb₀) t) ≠ 0) := by
  change 1 / 8 ≤ probability (fun t : Copies B K × N =>
    copyObserver i hi C hC noise hdim b₀ hb₀ T t.1 (noise t.2) ≠ 0)
  rw [probability_prod_average (fun L n =>
    copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0)]
  exact detection_average i hi C hC noise hdim b₀ hb₀ hbase T hr

end DFVSGames.Gadget.EnlargementConstruction
end

end OAI
