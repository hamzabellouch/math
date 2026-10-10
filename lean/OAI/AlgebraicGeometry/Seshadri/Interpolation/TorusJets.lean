import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.CyclicLattices

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
theorem triangle_cyclic_jet_test (p₀ p₁ p₂ : ℝ × ℝ) (H : ℝ) (hH : 0 < H)
    (r : ℕ) (hr : 0 < r) (i j : ℤ) (hprim : IsCoprime i j)
    (h01 : directionProjection i j p₀ ≤ directionProjection i j p₁)
    (h12 : directionProjection i j p₁ ≤ directionProjection i j p₂)
    (hrange : directionProjection i j p₂ - directionProjection i j p₀ =
      Real.sqrt ((r : ℝ) * H))
    (harea : triangleDoubleArea p₀ p₁ p₂ = H)
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ convexHull ℝ {p₀, p₁, p₂})
    (c : ℤ × ℤ → ℂ) (hc : ∀ p ∈ s, c p ≠ 0)
    (m : ℕ) (hm : Real.sqrt (H / r) < (m : ℝ))
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c)
      (cyclicTorusPoint ζ i j l).1 (cyclicTorusPoint ζ i j l).2 m := by
  classical
  by_contra! hall
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hζ0 : ζ ≠ 0 := (hζ.isUnit hr.ne').ne_zero
  have hmoment (l : ℕ) (hl : l < r) :
      MomentJetZero s (fun p => c p * ζ ^ ((l : ℤ) * latticeHeight i j p))
        (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m := by
    have h := mixedJetZero_moments s c (cyclicTorusPoint ζ i j l).1
      (cyclicTorusPoint ζ i j l).2
      (zpow_ne_zero _ hζ0) (zpow_ne_zero _ hζ0) m (hall ⟨l, hl⟩)
    apply h.congr s _ _ _ _ _ _ m
    · intro p _
      rw [mul_assoc, cyclicTorusPoint_character ζ hζ0]
    · intro _ _; rfl
    · intro _ _; rfl
  obtain ⟨e, he⟩ := hs
  let s' := s.filter (fun p => (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e)
  have hs' : s'.Nonempty := ⟨e, by simp [s', he]⟩
  have hcos : ∀ p ∈ s', (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  have hproject : MomentJetZero s' c (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m :=
    root_project_moments s c _ _ (latticeHeight i j) r m hr ζ hζ hmoment (latticeHeight i j e)
  obtain ⟨a, b, hbez⟩ := hprim
  let f := latticeCoord r i j a b e
  let F := latticeAffine r i j a b e
  have hinj : Set.InjOn f s' := (latticeCoord_injOn r i j a b e hbez).mono hcos
  have hjet := lattice_moments s' c r m hr i j a b e hbez hcos hproject
  have h01' : (F p₀).2 ≤ (F p₁).2 := by
    have h := div_nonneg (sub_nonneg.mpr h01) hrR.le
    rw [← latticeAffine_snd_sub r i j a b e p₀ p₁] at h
    exact sub_nonneg.mp h
  have h12' : (F p₁).2 ≤ (F p₂).2 := by
    have h := div_nonneg (sub_nonneg.mpr h12) hrR.le
    rw [← latticeAffine_snd_sub r i j a b e p₁ p₂] at h
    exact sub_nonneg.mp h
  have hrange' : (F p₂).2 - (F p₀).2 = Real.sqrt (H / r) := by
    rw [latticeAffine_snd_sub, hrange, sqrt_mul_div r hr H hH]
  have harea' : triangleDoubleArea (F p₀) (F p₁) (F p₂) = (Real.sqrt (H / r)) ^ 2 := by
    dsimp only [triangleDoubleArea, F]
    rw [latticeAffine_det r i j a b e hbez, abs_div, abs_of_pos hrR]
    change triangleDoubleArea p₀ p₁ p₂ / r = _
    rw [harea, Real.sq_sqrt (div_pos hH hrR).le]
  have hsupp' : ∀ q ∈ s'.image f, ((q.1 : ℝ), (q.2 : ℝ)) ∈
      convexHull ℝ {F p₀, F p₁, F p₂} := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [latticeCoord_cast r hr i j a b e p (hcos p hp)]
    have hmem : F ((p.1 : ℝ), (p.2 : ℝ)) ∈ F '' convexHull ℝ {p₀, p₁, p₂} :=
      Set.mem_image_of_mem F (hsupp p (Finset.mem_filter.mp hp).1)
    simpa only [AffineMap.image_convexHull, Set.image_insert_eq, Set.image_singleton] using hmem
  have hc' : ∀ q ∈ s'.image f, (c ∘ Function.invFunOn f s') q ≠ 0 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    simp only [Function.comp_apply, hinj.leftInvOn_invFunOn hp]
    exact hc p (Finset.mem_filter.mp hp).1
  exact triangle_euler_test (F p₀) (F p₁) (F p₂) (Real.sqrt (H / r))
    (Real.sqrt_pos.mpr (div_pos hH hrR)) h01' h12' hrange' harea'
    (s'.image f) (hs'.image f) hsupp' _ hc' m hm hjet

theorem scaled_compressed_triangle (d H t k : ℝ) :
    k • compressedTriangle d H t =
      convexHull ℝ {(k * (d * H * t / (1 + t)), 0),
        (-(k * (d * H / (1 + t))), 0), (0, k / d)} := by
  rw [compressedTriangle, ← convexHull_smul]
  simp only [Set.smul_set_insert, Set.smul_set_singleton, Prod.smul_mk, smul_eq_mul,
    mul_neg, mul_zero, mul_one_div]
  rw [Set.insert_comm]

theorem scaled_compressed_area (d H t k : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t) :
    triangleDoubleArea (k * (d * H * t / (1 + t)), 0)
      (-(k * (d * H / (1 + t))), 0) (0, k / d) = k ^ 2 * H := by
  have htp : 1 + t ≠ 0 := by positivity
  have heq : (-(k * (d * H / (1 + t))) - k * (d * H * t / (1 + t))) * (k / d) =
      -(k ^ 2 * H) := by
    field_simp
    ring
  dsimp [triangleDoubleArea]
  simp only [sub_zero, mul_zero, sub_self, zero_sub]
  rw [heq, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg k) hH.le)]

theorem sqrt_scale (k x : ℝ) (hk : 0 ≤ k) :
    Real.sqrt (k ^ 2 * x) = k * Real.sqrt x := by
  rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk]

theorem compressed_cyclic_jet_test (d H t : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t)
    (r : ℕ) (hr : 0 < r) (i j : ℤ) (hj : 0 < j) (hprim : IsCoprime i j)
    (hlen : (i : ℝ) / d + (j : ℝ) * (d * H * t / (1 + t)) = Real.sqrt ((r : ℝ) * H))
    (hsep : (j : ℝ) * (d * H / (1 + t)) < (i : ℝ) / d)
    (k m : ℕ) (hk : 0 < k) (hm : (k : ℝ) * Real.sqrt (H / r) < (m : ℝ))
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ (k : ℝ) • compressedTriangle d H t)
    (c : ℤ × ℤ → ℂ) (hc : ∀ p ∈ s, c p ≠ 0) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c)
      (cyclicTorusPoint ζ i j l).1 (cyclicTorusPoint ζ i j l).2 m := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  let A := d * H * t / (1 + t)
  let B := d * H / (1 + t)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have h01 : directionProjection i j ((k : ℝ) * A, 0) ≤
      directionProjection i j (-((k : ℝ) * B), 0) := by
    dsimp [directionProjection]
    nlinarith only [mul_pos hjR (mul_pos hkR hA), mul_pos hjR (mul_pos hkR hB)]
  have h12 : directionProjection i j (-((k : ℝ) * B), 0) ≤
      directionProjection i j (0, (k : ℝ) / d) := by
    have h := mul_le_mul_of_nonneg_left hsep.le hkR.le
    dsimp [directionProjection]
    dsimp [B] at *
    calc
      _ = (k : ℝ) * ((j : ℝ) * (d * H / (1 + t))) := by ring
      _ ≤ (k : ℝ) * ((i : ℝ) / d) := h
      _ = _ := by ring
  have hsqrt : Real.sqrt ((r : ℝ) * ((k : ℝ) ^ 2 * H)) =
      (k : ℝ) * Real.sqrt ((r : ℝ) * H) := by
    rw [show (r : ℝ) * ((k : ℝ) ^ 2 * H) = (k : ℝ) ^ 2 * ((r : ℝ) * H) by ring,
      sqrt_scale _ _ hkR.le]
  have hrange : directionProjection i j (0, (k : ℝ) / d) -
      directionProjection i j ((k : ℝ) * A, 0) =
      Real.sqrt ((r : ℝ) * ((k : ℝ) ^ 2 * H)) := by
    rw [hsqrt, ← hlen]
    dsimp [directionProjection, A]
    ring
  have hm' : Real.sqrt ((k : ℝ) ^ 2 * H / r) < (m : ℝ) := by
    rw [mul_div_assoc, sqrt_scale _ _ hkR.le]
    exact hm
  apply triangle_cyclic_jet_test ((k : ℝ) * A, 0) (-((k : ℝ) * B), 0)
    (0, (k : ℝ) / d) ((k : ℝ) ^ 2 * H) (mul_pos (sq_pos_of_pos hkR) hH)
    r hr i j hprim h01 h12 hrange (scaled_compressed_area d H t k hd hH ht)
    s hs _ c hc m hm' ζ hζ
  intro p hp
  simpa only [scaled_compressed_triangle] using hsupp p hp

theorem eventual_torus_jet_test (d H T : ℝ) (hd : 0 < d) (hH : 0 < H) (hT : 1 < T) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ t : ℝ, T < t ∧ ∃ points : Fin r → ℂ × ℂ,
        Function.Injective points ∧ (∀ l, (points l).1 ≠ 0 ∧ (points l).2 ≠ 0) ∧
        ∀ (k m : ℕ), 0 < k → 0 < m → (k : ℝ) * Real.sqrt (H / r) < (m : ℝ) →
          ∀ (s : Finset (ℤ × ℤ)), s.Nonempty →
            (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ (k : ℝ) • compressedTriangle d H t) →
            ∀ c : ℤ × ℤ → ℂ, (∀ p ∈ s, c p ≠ 0) →
              ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c) (points l).1 (points l).2 m := by
  have hlim : Filter.Tendsto (fun r : ℕ => Real.sqrt ((r : ℝ) * H))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hH)
  have hev := (hlim.eventually (Filter.eventually_ge_atTop (2 * (d * H)))).and
    (hlim.eventually (Filter.eventually_gt_atTop (8 * (1 + T) / d)))
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max r₀ 1, by omega, ?_⟩
  intro r hr
  have hrpos : 0 < r := by omega
  obtain ⟨hR1, hR2⟩ := hr₀ r (by omega)
  obtain ⟨t, i, j, ht, _hi, hj, hprim, hlen, hsep⟩ :=
    primitive_direction_coordinates d H T (Real.sqrt ((r : ℝ) * H)) hd hH hT hR1 hR2
  let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (r : ℂ))
  have hζ : IsPrimitiveRoot ζ r := Complex.isPrimitiveRoot_exp r hrpos.ne'
  have hζ0 : ζ ≠ 0 := (hζ.isUnit hrpos.ne').ne_zero
  refine ⟨t, ht, (fun l => cyclicTorusPoint ζ i j l),
    cyclicTorusPoint_injective ζ r hrpos hζ i j hprim, ?_, ?_⟩
  · intro l
    exact ⟨zpow_ne_zero _ hζ0, zpow_ne_zero _ hζ0⟩
  · intro k m hk _hm hm s hs hsupp c hc
    exact compressed_cyclic_jet_test d H t hd hH (by linarith) r hrpos i j hj hprim hlen hsep
      k m hk hm s hs hsupp c hc ζ hζ

open scoped BigOperators ContDiff
open Filter Topology


end MaximalSeshadri.Interpolation
end

end OAI
