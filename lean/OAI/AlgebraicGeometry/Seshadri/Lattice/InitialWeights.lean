import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Analytic.ConvergentSeries

namespace OAI


                                            
section

namespace MaximalSeshadri
open scoped BigOperators Topology
open Filter Set
noncomputable def exponentWeight (t : ℝ) (p : Exponent) : ℝ := p.1 + t * p.2

def StrictInitial (c : Exponent → ℂ) (t : ℝ) (e : Exponent) : Prop :=
  c e ≠ 0 ∧ ∀ p, c p ≠ 0 → p ≠ e → exponentWeight t e < exponentWeight t p

def LexInitial (c : Exponent → ℂ) (t : ℝ) (e : Exponent) : Prop :=
  c e ≠ 0 ∧ ∀ p, c p ≠ 0 →
    exponentWeight t e ≤ exponentWeight t p ∧
    (exponentWeight t e = exponentWeight t p → e.2 ≤ p.2)

lemma exponentWeight_nonneg (t : ℝ) (ht : 0 ≤ t) (p : Exponent) :
    0 ≤ exponentWeight t p := by unfold exponentWeight; positivity

lemma exponentWeight_mono (t u : ℝ) (htu : t ≤ u) (p : Exponent) :
    exponentWeight t p ≤ exponentWeight u p := by
  unfold exponentWeight
  gcongr

lemma continuous_exponentWeight (p : Exponent) : Continuous (fun t => exponentWeight t p) := by
  unfold exponentWeight
  fun_prop

lemma finite_boundedWeight (t M : ℝ) (ht : 0 < t) :
    {p : Exponent | exponentWeight t p < M}.Finite := by
  refine (Set.finite_Iic (⟨⌈M⌉₊, ⌈M / t⌉₊⟩ : Exponent)).subset ?_
  intro p hp
  change p.1 ≤ ⌈M⌉₊ ∧ p.2 ≤ ⌈M / t⌉₊
  have hp' : (p.1 : ℝ) + t * p.2 < M := hp
  have h1 : (p.1 : ℝ) ≤ M := by nlinarith [Nat.cast_nonneg (α := ℝ) p.2]
  have h2 : (p.2 : ℝ) ≤ M / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) p.1]
  exact ⟨(Nat.cast_le (α := ℝ)).mp (h1.trans (Nat.le_ceil M)),
    (Nat.cast_le (α := ℝ)).mp (h2.trans (Nat.le_ceil (M / t)))⟩

lemma LexInitial.beta_lt_of_eq_weight {c : Exponent → ℂ} {t : ℝ} {e p : Exponent}
    (he : LexInitial c t e) (hp : c p ≠ 0) (hne : p ≠ e)
    (hw : exponentWeight t e = exponentWeight t p) : e.2 < p.2 := by
  have hle := (he.2 p hp).2 hw
  refine lt_of_le_of_ne hle ?_
  intro hβ
  apply hne
  apply Prod.ext
  · have hα : (e.1 : ℝ) = p.1 := by simpa [exponentWeight, hβ] using hw
    exact (Nat.cast_inj.mp hα).symm
  · exact hβ.symm

theorem exists_strictWeight_of_lex {ι : Type*} [Finite ι]
    (c : ι → Exponent → ℂ) (e : ι → Exponent) (t : ℝ) (ht : 0 < t)
    (he : ∀ i, LexInitial (c i) t (e i)) :
    ∃ u : ℝ, t < u ∧ ∀ i, StrictInitial (c i) u (e i) := by
  classical
  let := Fintype.ofFinite ι
  let M : ℝ := 1 + ∑ i, exponentWeight t (e i)
  have hem (i : ι) : exponentWeight t (e i) < M := by
    have hh := Finset.single_le_sum (f := fun i => exponentWeight t (e i))
      (fun i _ => exponentWeight_nonneg t ht.le (e i)) (Finset.mem_univ i)
    dsimp [M]
    linarith
  let B : Set Exponent := {p | exponentWeight t p < M}
  have hB : B.Finite := finite_boundedWeight t M ht
  let := hB.fintype
  have hlow : ∀ᶠ u : ℝ in 𝓝[>] t, ∀ i : ι, ∀ p : B,
      c i p ≠ 0 → (p : Exponent) ≠ e i → exponentWeight u (e i) < exponentWeight u p := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro p
    by_cases hp : c i p = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hp).elim)
    by_cases hpe : (p : Exponent) = e i
    · exact Filter.Eventually.of_forall (fun _ _ h => (h hpe).elim)
    by_cases hw : exponentWeight t (e i) < exponentWeight t p
    · have hh : Continuous (fun u => exponentWeight u p - exponentWeight u (e i)) :=
        (continuous_exponentWeight p).sub (continuous_exponentWeight (e i))
      filter_upwards [((hh.tendsto t).eventually (lt_mem_nhds (sub_pos.mpr hw))).filter_mono
          nhdsWithin_le_nhds] with u hu _ _
      exact sub_pos.mp hu
    · have heq := le_antisymm (he i |>.2 p hp).1 (le_of_not_gt hw)
      have hβ := (he i).beta_lt_of_eq_weight hp hpe heq
      filter_upwards [self_mem_nhdsWithin] with u hu _ _
      have hβR : ((e i).2 : ℝ) < (p : Exponent).2 := by exact_mod_cast hβ
      have hmul := mul_pos (sub_pos.mpr hu) (sub_pos.mpr hβR)
      dsimp [exponentWeight] at heq ⊢
      nlinarith
  have hbelow : ∀ᶠ u : ℝ in 𝓝[>] t, ∀ i : ι, exponentWeight u (e i) < M := by
    apply Filter.eventually_all.mpr
    intro i
    exact (((continuous_exponentWeight (e i)).tendsto t).eventually
      (gt_mem_nhds (hem i))).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] t, t < u := self_mem_nhdsWithin
  obtain ⟨u, htu, hlu, hbu⟩ := (hpos.and (hlow.and hbelow)).exists
  refine ⟨u, htu, fun i => ⟨(he i).1, ?_⟩⟩
  intro p hp hpe
  by_cases hpb : p ∈ B
  · exact hlu i ⟨p, hpb⟩ hp hpe
  · have hM : M ≤ exponentWeight t p := le_of_not_gt hpb
    exact (hbu i).trans_le (hM.trans (exponentWeight_mono t u htu.le p))

noncomputable def lexKey (t : ℝ) (p : Exponent) : ℝ ×ₗ ℕ :=
  toLex (exponentWeight t p, p.2)

lemma lexKey_le_iff (t : ℝ) (p q : Exponent) :
    lexKey t p ≤ lexKey t q ↔ exponentWeight t p ≤ exponentWeight t q ∧
      (exponentWeight t p = exponentWeight t q → p.2 ≤ q.2) :=
  Prod.Lex.toLex_le_toLex'

lemma lexKey_injective (t : ℝ) : Function.Injective (lexKey t) := by
  intro p q h
  have hy : p.2 = q.2 := congrArg (fun z : ℝ ×ₗ ℕ => (ofLex z).2) h
  have hw : exponentWeight t p = exponentWeight t q :=
    congrArg (fun z : ℝ ×ₗ ℕ => (ofLex z).1) h
  apply Prod.ext
  · have hα : (p.1 : ℝ) = q.1 := by simpa [exponentWeight, hy] using hw
    exact Nat.cast_inj.mp hα
  · exact hy

lemma LexInitial.key_le {c : Exponent → ℂ} {t : ℝ} {e : Exponent}
    (h : LexInitial c t e) {p : Exponent} (hp : c p ≠ 0) :
    lexKey t e ≤ lexKey t p := (lexKey_le_iff t e p).mpr (h.2 p hp)

lemma LexInitial.unique {c : Exponent → ℂ} {t : ℝ} {e f : Exponent}
    (he : LexInitial c t e) (hf : LexInitial c t f) : e = f :=
  lexKey_injective t (le_antisymm (he.key_le hf.1) (hf.key_le he.1))

theorem exists_lexInitial (c : Exponent → ℂ) (t : ℝ) (ht : 0 < t)
    (hc : c ≠ 0) : ∃ e, LexInitial c t e := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra! h
    exact hc (funext h)
  let B : Set Exponent := {q | c q ≠ 0 ∧ exponentWeight t q < exponentWeight t p + 1}
  have hB : B.Finite :=
    (finite_boundedWeight t (exponentWeight t p + 1) ht).subset fun _ h => h.2
  have hpB : p ∈ B := ⟨hp, lt_add_one _⟩
  obtain ⟨e, heB, he⟩ := Set.exists_min_image B (lexKey t) hB ⟨p, hpB⟩
  refine ⟨e, heB.1, fun q hq => (lexKey_le_iff t e q).mp ?_⟩
  by_cases hqB : q ∈ B
  · exact he q hqB
  · have hqp : exponentWeight t p + 1 ≤ exponentWeight t q := by
      by_contra! h
      exact hqB ⟨hq, h⟩
    have hep := ((lexKey_le_iff t e p).mp (he p hpB)).1
    apply Prod.Lex.toLex_le_toLex.mpr
    exact Or.inl (by dsimp [lexKey]; linarith)

theorem linearIndependent_of_lexInitial {ι : Type*} (c : ι → Exponent → ℂ)
    (e : ι → Exponent) (t : ℝ) (he : ∀ i, LexInitial (c i) t (e i))
    (hinj : Function.Injective e) : LinearIndependent ℂ c := by
  classical
  rw [linearIndependent_iff']
  intro s a hsum i hi
  by_contra hai
  let A := s.filter (fun j => a j ≠ 0)
  have hAi : i ∈ A := Finset.mem_filter.mpr ⟨hi, hai⟩
  obtain ⟨j, hjA, hj⟩ := A.exists_min_image (fun j => lexKey t (e j)) ⟨i, hAi⟩
  have hjS := (Finset.mem_filter.mp hjA).1
  have haj := (Finset.mem_filter.mp hjA).2
  have hzero (l : ι) (hl : l ∈ s) (hlj : l ≠ j) : a l * c l (e j) = 0 := by
    by_cases hal : a l = 0
    · simp [hal]
    have hlA : l ∈ A := Finset.mem_filter.mpr ⟨hl, hal⟩
    have hcl : c l (e j) = 0 := by
      by_contra hcl
      have hkey := le_antisymm (hj l hlA) ((he l).key_le hcl)
      have hej : e j = e l := lexKey_injective t hkey
      exact hlj (hinj hej).symm
    simp [hcl]
  have hs : (∑ l ∈ s, a l * c l (e j)) = a j * c j (e j) := by
    exact Finset.sum_eq_single j hzero (fun h => (h hjS).elim)
  have hh := congrFun hsum (e j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hh
  rw [hs] at hh
  exact (mul_ne_zero haj (he j).1) hh

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

end MaximalSeshadri


end

end OAI
