import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Conic
noncomputable section
open Set
open scoped Topology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

omit [ContinuousSMul ℝ F] in
lemma add_mem_interior_cone (K : ConvexCone ℝ F) {a b : F}
    (ha : a ∈ K) (hb : b ∈ interior (K : Set F)) :
    a + b ∈ interior (K : Set F) := by
  have ho : IsOpen {z : F | z - a ∈ interior (K : Set F)} :=
    isOpen_interior.preimage (continuous_id.sub continuous_const)
  have hs : {z : F | z - a ∈ interior (K : Set F)} ⊆ (K : Set F) := by
    intro z hz
    have := K.add_mem ha (interior_subset hz)
    simp only [add_sub_cancel] at this
    exact this
  apply interior_maximal hs ho
  simpa using hb

omit [IsTopologicalAddGroup F] in
lemma smul_mem_interior_cone (K : ConvexCone ℝ F) {a : ℝ} {b : F}
    (ha : 0 < a) (hb : b ∈ interior (K : Set F)) :
    a • b ∈ interior (K : Set F) := by
  have ho : IsOpen {z : F | a⁻¹ • z ∈ interior (K : Set F)} :=
    isOpen_interior.preimage (continuous_const.smul continuous_id)
  have hs : {z : F | a⁻¹ • z ∈ interior (K : Set F)} ⊆ (K : Set F) := by
    intro z hz
    have := K.smul_mem ha (interior_subset hz)
    simp only [smul_smul, mul_inv_cancel₀ ha.ne', one_smul] at this
    exact this
  apply interior_maximal hs ho
  change a⁻¹ • (a • b) ∈ interior (K : Set F)
  simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using hb

def strictEpigraph (K : ConvexCone ℝ F) (D : Set E) (g : E → F) (f : E → ℝ) :
    Set (F × ℝ) :=
  {z | ∃ x ∈ D, z.1 - g x ∈ interior (K : Set F) ∧ f x < z.2}

omit [AddCommGroup E] [Module ℝ E] [ContinuousSMul ℝ F] in
lemma strictEpigraph_open (K : ConvexCone ℝ F) (D : Set E) (g : E → F) (f : E → ℝ) :
    IsOpen (strictEpigraph K D g f) := by
  have he : strictEpigraph K D g f =
      ⋃ x ∈ D, {z : F × ℝ | z.1 - g x ∈ interior (K : Set F)} ∩
        {z : F × ℝ | f x < z.2} := by
    ext z
    simp only [strictEpigraph, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    aesop
  rw [he]
  exact isOpen_iUnion fun x => isOpen_iUnion fun _ =>
    (isOpen_interior.preimage (continuous_fst.sub continuous_const)).inter
      (isOpen_lt continuous_const continuous_snd)

lemma strictEpigraph_convex (K : ConvexCone ℝ F) (D : Set E) (g : E → F) (f : E → ℝ)
    (hD : Convex ℝ D) (hf : ConvexOn ℝ D f)
    (hg : ∀ x ∈ D, ∀ y ∈ D, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      a • g x + b • g y - g (a • x + b • y) ∈ K) :
    Convex ℝ (strictEpigraph K D g f) := by
  rintro z ⟨x, hx, hzx, hfx⟩ w ⟨y, hy, hwy, hfy⟩ a b ha hb hab
  refine ⟨a • x + b • y, hD hx hy ha hb hab, ?_, ?_⟩
  · have hi := K.convex.interior hzx hwy ha hb hab
    have h := add_mem_interior_cone K (hg x hx y hy a b ha hb hab) hi
    convert h using 1
    dsimp
    module
  · have h := hf.2 hx hy ha hb hab
    have hh : a * f x + b * f y < a * z.2 + b * w.2 := by
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb' : b = 1 := by linarith
        simpa [hb'] using hfy
      · have h1 := mul_lt_mul_of_pos_left hfx ha'
        have h2 := mul_le_mul_of_nonneg_left hfy.le hb
        linarith
    exact h.trans_lt hh

lemma nonpos_of_bounded_ray {a b c : ℝ} (h : ∀ r : ℝ, 0 ≤ r → a + r*b < c) : b ≤ 0 := by
  by_contra hn
  have hb : 0 < b := lt_of_not_ge hn
  have hr : 0 ≤ max 0 ((c-a)/b) + 1 := by positivity
  have hh := h _ hr
  have hmax : (c-a)/b ≤ max 0 ((c-a)/b) := le_max_right _ _
  have hm := (div_le_iff₀ hb).mp hmax
  nlinarith

theorem multiplier_rule (K : ConvexCone ℝ F) (h0 : (0 : F) ∈ K)
    (D : Set E) (g : E → F) (f : E → ℝ)
    (hD : Convex ℝ D) (hf : ConvexOn ℝ D f)
    (hg : ∀ x ∈ D, ∀ y ∈ D, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      a • g x + b • g y - g (a • x + b • y) ∈ K)
    (x₀ : E) (hx₀ : x₀ ∈ D) (hfeas : -g x₀ ∈ K)
    (hmin : ∀ x ∈ D, -g x ∈ K → f x₀ ≤ f x)
    (xs : E) (hxs : xs ∈ D) (hstrict : -g xs ∈ interior (K : Set F)) :
    ∃ p : StrongDual ℝ F,
      (∀ k ∈ K, 0 ≤ p k) ∧ p (g x₀) = 0 ∧
      ∀ x ∈ D, f x₀ ≤ f x + p (g x) := by
  have hn : (0, f x₀) ∉ strictEpigraph K D g f := by
    rintro ⟨x, hx, hc, hfx⟩
    have hfe : -g x ∈ K := interior_subset (by simpa using hc)
    exact (not_lt_of_ge (hmin x hx hfe)) hfx
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point
    (strictEpigraph_convex K D g f hD hf hg) (strictEpigraph_open K D g f) hn
  let q : StrongDual ℝ F := l.comp (ContinuousLinearMap.inl ℝ F ℝ)
  let a : ℝ := l (0, 1)
  have hsplit (y : F) (t : ℝ) : l (y,t) = q y + t*a := by
    have he : (y,t) = (y,0) + t • (0,1) := by simp
    rw [he, map_add, map_smul]
    rfl
  have haneg : a < 0 := by
    let t := max (f xs + 1) (f x₀)
    have ht : f xs < t := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hv : f x₀ ≤ t := le_max_right _ _
    have hs := hl (0,t) ⟨xs, hxs, by simpa using hstrict, ht⟩
    rw [hsplit, hsplit, map_zero, zero_add, zero_add] at hs
    by_contra hh
    have := mul_le_mul_of_nonneg_right hv (le_of_not_gt hh)
    linarith
  have hq (k : F) (hk : k ∈ K) : q k ≤ 0 := by
    have hr (r : ℝ) (hr : 0 ≤ r) :
        (f xs + 1)*a + r * q k < f x₀*a := by
      have hkr : r • k ∈ K := by
        rcases eq_or_lt_of_le hr with rfl | hr
        · simpa using h0
        · exact K.smul_mem hr hk
      have hs := hl (r • k, f xs + 1)
        ⟨xs, hxs, by simpa [sub_eq_add_neg] using add_mem_interior_cone K hkr hstrict,
          by linarith⟩
      rw [hsplit, hsplit, map_zero, zero_add, map_smul, smul_eq_mul] at hs
      linarith
    exact nonpos_of_bounded_ray hr
  have hlim (x : E) (hx : x ∈ D) : q (g x) + f x*a ≤ f x₀*a := by
    have hε (ε : ℝ) (hε : 0 < ε) :
        q (g x) + f x*a + ε*(q (-g xs) + a) < f x₀*a := by
      have hs := hl (g x + ε • (-g xs), f x + ε)
        ⟨x, hx, by simpa using smul_mem_interior_cone K hε hstrict, by linarith⟩
      rw [hsplit, hsplit, map_zero, zero_add, map_add, map_smul, smul_eq_mul] at hs
      nlinarith
    by_contra hh
    have hd : 0 < q (g x) + f x*a - f x₀*a := by linarith
    let ε := (q (g x) + f x*a - f x₀*a) / (|q (-g xs)+a|+1) / 2
    have hεpos : 0 < ε := by dsimp [ε]; positivity
    have hhε := hε ε hεpos
    have heq : ε * (|q (-g xs)+a|+1) * 2 = q (g x) + f x*a - f x₀*a := by
      dsimp [ε]
      field_simp
    have hab := neg_abs_le (q (-g xs)+a)
    have hmul := mul_le_mul_of_nonneg_left hab hεpos.le
    nlinarith
  let p : StrongDual ℝ F := a⁻¹ • q
  have hp (k : F) (hk : k ∈ K) : 0 ≤ p k := by
    change 0 ≤ a⁻¹ * q k
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr haneg.le) (hq k hk)
  have hlag (x : E) (hx : x ∈ D) : f x₀ ≤ f x + p (g x) := by
    have hh := hlim x hx
    change f x₀ ≤ f x + a⁻¹ * q (g x)
    have hm := mul_le_mul_of_nonpos_right hh (inv_nonpos.mpr haneg.le)
    calc
      f x₀ = (f x₀ * a) * a⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ haneg.ne, mul_one]
      _ ≤ (q (g x) + f x*a) * a⁻¹ := hm
      _ = f x + a⁻¹ * q (g x) := by
        rw [add_mul, mul_assoc, mul_inv_cancel₀ haneg.ne, mul_one]
        ring
  refine ⟨p, hp, ?_, hlag⟩
  have h1 := hp (-g x₀) hfeas
  have h2 := hlag x₀ hx₀
  rw [map_neg] at h1
  linarith
end
end CurrentKS.Conic

end OAI
