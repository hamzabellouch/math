import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.WeightedRescaling

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set
lemma DerivativeSummable.zero (R : ℝ) : DerivativeSummable 0 R := by
  intro a b
  convert (summable_zero : Summable (fun _ : Exponent => (0 : ℝ))) using 1
  ext p
  simp [derivativeMajorant]

lemma DerivativeSummable.add {c d : Exponent → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : DerivativeSummable c R) (hd : DerivativeSummable d R) :
    DerivativeSummable (c + d) R := by
  intro a b
  apply Summable.of_nonneg_of_le (fun p => by unfold derivativeMajorant; positivity)
    (fun p => ?_) ((hc a b).add (hd a b))
  simp only [derivativeMajorant, Pi.add_apply]
  calc
    _ ≤ (‖c p‖ + ‖d p‖) * ((p.1.descFactorial a : ℝ) * R ^ (p.1 - a)) *
        ((p.2.descFactorial b : ℝ) * R ^ (p.2 - b)) := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by ring

lemma DerivativeSummable.smul {c : Exponent → ℂ} {R : ℝ}
    (hc : DerivativeSummable c R) (v : ℂ) : DerivativeSummable (v • c) R := by
  intro a b
  have hh : derivativeMajorant (v • c) R a b = fun p => ‖v‖ * derivativeMajorant c R a b p := by
    funext p
    simp only [derivativeMajorant, Pi.smul_apply, smul_eq_mul, norm_mul]
    ring
  rw [hh]
  exact (hc a b).mul_left ‖v‖

def derivativeSeriesSubmodule (R : ℝ) (hR : 0 ≤ R) : Submodule ℂ (Exponent → ℂ) where
  carrier := {c | DerivativeSummable c R}
  zero_mem' := DerivativeSummable.zero R
  add_mem' := DerivativeSummable.add hR
  smul_mem' v _ hc := hc.smul v

theorem exists_commonDerivativeRadius (V : Submodule ℂ (Exponent → ℂ))
    [FiniteDimensional ℂ V] (hc : ∀ c ∈ V, ConvergentSeries c) :
    ∃ R : ℝ, 0 < R ∧ ∀ c ∈ V, DerivativeSummable c R := by
  classical
  let b := Module.finBasis ℂ V
  have hh (i : Fin (Module.finrank ℂ V)) : ConvergentSeries (b i : Exponent → ℂ) :=
    hc _ (b i).property
  choose ρ hρ ha using hh
  have he : ∀ᶠ R : ℝ in 𝓝[>] 0, ∀ i, R < ρ i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (gt_mem_nhds (hρ i)).filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ R : ℝ in 𝓝[>] 0, 0 < R := self_mem_nhdsWithin
  obtain ⟨R, hR, hRi⟩ := (hp.and he).exists
  have hb (i) : DerivativeSummable (b i : Exponent → ℂ) R :=
    derivativeSummable_of_absolute _ (ρ i) R (hρ i) hR (hRi i) (ha i)
  refine ⟨R, hR, ?_⟩
  intro c hcV
  let f : V := ⟨c, hcV⟩
  let D := derivativeSeriesSubmodule R hR.le
  have hm : ((∑ i, b.repr f i • b i : V) : Exponent → ℂ) ∈ D := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact D.sum_mem (fun i _ => D.smul_mem _ (hb i))
  change DerivativeSummable ((∑ i, b.repr f i • b i : V) : Exponent → ℂ) R at hm
  simpa only [b.sum_repr f] using hm

noncomputable def seriesPartialMap (V : Submodule ℂ (Exponent → ℂ)) (R : ℝ)
    (hs : ∀ c ∈ V, DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) : V →ₗ[ℂ] ℂ where
  toFun f := seriesPartial f a b x z
  map_add' f g := by
    simp only [seriesPartial, Submodule.coe_add, Pi.add_apply, add_mul]
    exact (summable_seriesPartial f R (hs f f.property) a b x z hx hz).tsum_add
      (summable_seriesPartial g R (hs g g.property) a b x z hx hz)
  map_smul' v f := by
    simp only [seriesPartial, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_assoc, RingHom.id_apply]
    exact tsum_mul_left

noncomputable def seriesJetMap (V : Submodule ℂ (Exponent → ℂ)) (R : ℝ)
    (hs : ∀ c ∈ V, DerivativeSummable c R) (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (hp : ∀ j, ‖(p j).1‖ < R ∧ ‖(p j).2‖ < R) : V →ₗ[ℂ] (JetIndex r m → ℂ) :=
  LinearMap.pi fun j =>
    if j.2.1.val + j.2.2.val < m then
      seriesPartialMap V R hs j.2.1 j.2.2 (p j.1).1 (p j.1).2
        (hp j.1).1.le (hp j.1).2.le
    else 0

lemma seriesJetMap_eq (V : Submodule ℂ (Exponent → ℂ)) (R : ℝ)
    (hs : ∀ c ∈ V, DerivativeSummable c R) (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (hp : ∀ j, ‖(p j).1‖ < R ∧ ‖(p j).2‖ < R) (f : V) :
    seriesJetMap V R hs r m p hp f = finiteJetColumn r m p (seriesEval f) := by
  ext j
  simp only [seriesJetMap, LinearMap.pi_apply, finiteJetColumn]
  split_ifs
  · exact (mixedDeriv_seriesEval f R (hs f f.property) j.2.1 j.2.2
      (p j.1).1 (p j.1).2 (hp j.1).1 (hp j.1).2).symm
  · rfl

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


end MaximalSeshadri.Interpolation
end

end OAI
