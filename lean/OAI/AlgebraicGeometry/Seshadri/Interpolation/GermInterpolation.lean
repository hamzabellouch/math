import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.TorusJets
import OAI.AlgebraicGeometry.Seshadri.Interpolation.QuadrilateralRows
import OAI.AlgebraicGeometry.Seshadri.Interpolation.InitialBasis

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set
def initialExponentSet (V : Submodule ℂ (Exponent → ℂ)) (t : ℝ) : Set Exponent :=
  {e | ∃ c ∈ V, LexInitial c t e}

theorem exists_initial_basis (V : Submodule ℂ (Exponent → ℂ))
    [FiniteDimensional ℂ V] (t : ℝ) (ht : 0 < t) :
    (initialExponentSet V t).Finite ∧
      ∃ b : Module.Basis (initialExponentSet V t) ℂ V,
        ∀ e, LexInitial (b e : Exponent → ℂ) t e := by
  classical
  let E := initialExponentSet V t
  have hex (e : E) : ∃ c : V, LexInitial (c : Exponent → ℂ) t e := by
    obtain ⟨c, hc, he⟩ := e.property
    exact ⟨⟨c, hc⟩, he⟩
  choose c hc using hex
  have hli : LinearIndependent ℂ c := by
    apply LinearIndependent.of_comp V.subtype
    exact linearIndependent_of_lexInitial (fun e => (c e : Exponent → ℂ))
      (fun e => e.val) t hc Subtype.val_injective
  have : Finite E := hli.finite
  let := Fintype.ofFinite E
  let ev : V →ₗ[ℂ] (E → ℂ) := LinearMap.pi (fun e => (LinearMap.proj e.val).comp V.subtype)
  have hev : Function.Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro f hf
    by_contra hf0
    have hcoeff : (f : Exponent → ℂ) ≠ 0 := by
      intro h
      exact hf0 (Subtype.ext h)
    obtain ⟨e, he⟩ := exists_lexInitial f t ht hcoeff
    let ee : E := ⟨e, ⟨f, f.property, he⟩⟩
    have hh := congrFun (LinearMap.mem_ker.mp hf) ee
    exact he.1 hh
  have hcard : Fintype.card E = Module.finrank ℂ V := by
    apply le_antisymm hli.fintype_card_le_finrank
    simpa only [Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective hev
  refine ⟨Set.toFinite _, ?_⟩
  refine ⟨Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge, ?_⟩
  intro e
  simpa only [Module.Basis.mk_apply] using hc e

theorem card_initialExponentSet (V : Submodule ℂ (Exponent → ℂ))
    [FiniteDimensional ℂ V] (t : ℝ) (ht : 0 < t) :
    Nat.card (initialExponentSet V t) = Module.finrank ℂ V := by
  classical
  obtain ⟨hE, b, _⟩ := exists_initial_basis V t ht
  let := hE.fintype
  simpa only [Nat.card_eq_fintype_card] using (Module.finrank_eq_card_basis b).symm

theorem initial_monomial_jet_transfer (V : Submodule ℂ (Exponent → ℂ))
    [FiniteDimensional ℂ V] (hc : ∀ c ∈ V, ConvergentSeries c)
    (t : ℝ) (ht : 0 < t) (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (hp : Function.Injective p)
    (hjet : LinearIndependent ℂ (fun e : initialExponentSet V t =>
      finiteJetColumn r m p (fun x z => x ^ e.val.1 * z ^ e.val.2))) :
    ∃ R : ℝ, 0 < R ∧ (∀ c ∈ V, DerivativeSummable c R) ∧
      ∀ ε : ℝ, 0 < ε → ∃ q : Fin r → ℂ × ℂ, Function.Injective q ∧
        (∀ j, ‖(q j).1‖ < min ε R ∧ ‖(q j).2‖ < min ε R) ∧
        Function.Injective (fun f : V => finiteJetColumn r m q (seriesEval f)) := by
  classical
  obtain ⟨hE, b, hb⟩ := exists_initial_basis V t ht
  have := hE.to_subtype
  have hc' (e : initialExponentSet V t) : ConvergentSeries (b e : Exponent → ℂ) :=
    hc _ (b e).property
  obtain ⟨u, htu, hu⟩ := exists_strictWeight_of_lex
    (fun e => (b e : Exponent → ℂ)) (fun e => e.val) t ht hb
  obtain ⟨R, hR, hDR⟩ := exists_commonDerivativeRadius V hc
  refine ⟨R, hR, hDR, ?_⟩
  intro ε hε
  obtain ⟨q, hqi, hqn, hqj⟩ := initial_monomial_jet_transfer_strict
    (fun e => (b e : Exponent → ℂ)) (fun e => e.val) u (ht.trans htu) hu hc'
    r m p hp hjet (min ε R) (lt_min hε hR)
  have hqR (j) : ‖(q j).1‖ < R ∧ ‖(q j).2‖ < R :=
    ⟨(hqn j).1.trans_le (min_le_right _ _), (hqn j).2.trans_le (min_le_right _ _)⟩
  refine ⟨q, hqi, hqn, ?_⟩
  have hjli : LinearIndependent ℂ (seriesJetMap V R hDR r m q hqR ∘ b) := by
    simpa only [Function.comp_def, seriesJetMap_eq] using hqj
  have hinj := LinearMap.injective_of_linearIndependent b.span_eq hjli
  intro f g hfg
  apply hinj
  simpa only [seriesJetMap_eq] using hfg

theorem rowTriangle_scaled (d H t k : ℝ) :
    rowTriangle (k * (d * H * t / (1 + t))) (k * (d * H / (1 + t))) (k / d) =
      k • compressedTriangle d H t := by
  rw [scaled_compressed_triangle, rowTriangle, Set.insert_comm]

theorem exists_node_weight_range (d H : ℝ) (hd : 0 < d) (hH : 0 < H) :
    ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T < t → d ^ 2 * H * t < (1 + t) ^ 2 := by
  refine ⟨d ^ 2 * H + 2, ?_, ?_⟩
  · have hpos : 0 < d ^ 2 * H := mul_pos (sq_pos_of_pos hd) hH
    linarith
  intro t ht
  have hpos : 0 < d ^ 2 * H := mul_pos (sq_pos_of_pos hd) hH
  have ht0 : 0 < t := by linarith
  nlinarith [mul_pos ht0 (sub_pos.mpr ht)]

theorem scaled_node_parameters (d H t k : ℝ) (hd : 0 < d) (hH : 0 < H)
    (ht : 0 < t) (hk : 0 < k) (hweight : d ^ 2 * H * t < (1 + t) ^ 2) :
    (k * (d * H * t / (1 + t))) * (k * (d * H / (1 + t))) ≤
      (k / d) * (k * (d * H * t / (1 + t)) + k * (d * H / (1 + t))) := by
  have hden : 0 < 1 + t := by positivity
  have heq : (k / d) * (k * (d * H * t / (1 + t)) + k * (d * H / (1 + t))) =
      k ^ 2 * H := by
    field_simp; ring
  rw [heq]
  have hmul : d ^ 2 * H * t * (k ^ 2 * H) ≤ (1 + t) ^ 2 * (k ^ 2 * H) :=
    mul_le_mul_of_nonneg_right hweight.le (by positivity)
  have heq2 : (k * (d * H * t / (1 + t))) * (k * (d * H / (1 + t))) *
      (1 + t) ^ 2 = d ^ 2 * H * t * (k ^ 2 * H) := by
    field_simp
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hden)).mp
  rw [heq2, mul_comm (k ^ 2 * H)]
  exact hmul

theorem eventual_germ_jet_test (d H T : ℝ) (hd : 0 < d) (hH : 0 < H) (hT : 1 < T)
    (hweight : ∀ t : ℝ, T < t → d ^ 2 * H * t < (1 + t) ^ 2)
    (V : ℕ → Submodule ℂ (Exponent → ℂ))
    [∀ k, FiniteDimensional ℂ (V k)]
    (hconv : ∀ k c, c ∈ V k → ConvergentSeries c)
    (hbound : ∀ k, 0 < k → ∀ t, T < t → ∀ e ∈ initialExponentSet (V k) t,
      ((e.1 : ℝ), (e.2 : ℝ)) ∈ nodeQuadrilateral
        ((k : ℝ) * (d * H * t / (1 + t)))
        ((k : ℝ) * (d * H / (1 + t))) ((k : ℝ) / d)) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∀ k m : ℕ, 0 < k → 0 < m → (k : ℝ) * Real.sqrt (H / r) < (m : ℝ) →
      ∃ R : ℝ, 0 < R ∧ (∀ c ∈ V k, DerivativeSummable c R) ∧
        ∀ ε : ℝ, 0 < ε → ∃ q : Fin r → ℂ × ℂ, Function.Injective q ∧
          (∀ j, ‖(q j).1‖ < min ε R ∧ ‖(q j).2‖ < min ε R) ∧
          Function.Injective (fun f : V k => finiteJetColumn r m q (seriesEval f)) := by
  classical
  obtain ⟨r₀, hr₀, htorus⟩ := eventual_torus_jet_test d H T hd hH hT
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr k m hk hm hkm
  obtain ⟨t, ht, p, hpi, hpn, hp⟩ := htorus r hr
  have ht0 : 0 < t := by linarith
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨hE, _, _⟩ := exists_initial_basis (V k) t ht0
  let s := hE.toFinset
  have hmem (e : Exponent) : e ∈ s ↔ e ∈ initialExponentSet (V k) t := hE.mem_toFinset
  have htest : ∀ s : Finset (ℤ × ℤ), s.Nonempty →
      (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ rowTriangle
        ((k : ℝ) * (d * H * t / (1 + t)))
        ((k : ℝ) * (d * H / (1 + t))) ((k : ℝ) / d)) →
      ∀ c : ℤ × ℤ → ℂ, (∀ p ∈ s, c p ≠ 0) →
        ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c) (p l).1 (p l).2 m := by
    simpa only [rowTriangle_scaled] using hp k m hk hm hkm
  obtain ⟨q, hqi, _, hq⟩ := quadrilateral_jet_rank_of_triangle_test
    ((k : ℝ) * (d * H * t / (1 + t)))
    ((k : ℝ) * (d * H / (1 + t))) ((k : ℝ) / d)
    (by positivity) (by positivity) (by positivity)
    (scaled_node_parameters d H t k hd hH ht0 hk0 (hweight t ht))
    r m p hpi hpn htest s (fun e he => hbound k hk t ht e ((hmem e).mp he))
  have hq' : LinearIndependent ℂ (fun e : initialExponentSet (V k) t =>
      finiteJetColumn r m q (fun x z => x ^ e.val.1 * z ^ e.val.2)) := by
    let f : initialExponentSet (V k) t → s := fun e => ⟨e.val, (hmem e.val).mpr e.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun e : s => e.val) h
    exact hq.comp f hf
  exact initial_monomial_jet_transfer (V k) (hconv k) t ht0 r m q hqi hq'

end MaximalSeshadri.Interpolation

end



end OAI
