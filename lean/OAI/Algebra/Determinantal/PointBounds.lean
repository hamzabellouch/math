import OAI.Algebra.Determinantal.LinearForms

namespace OAI

namespace PermanentBorder.Multigraded
section AffineCokernel
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K W]

theorem affine_cokernel_polynomial (f g : V →ₗ[K] W) :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ t : K, p.eval t ≠ 0 →
      Module.finrank K (W ⧸ LinearMap.range ((1-t) • f + t • g)) ≤
        Module.finrank K (W ⧸ LinearMap.range f) := by
  classical
  let b := Module.finBasis K (LinearMap.range f)
  choose z hz using fun i => (b i).property
  have hli : LinearIndependent K (fun i => f (z i)) := by
    have h := b.linearIndependent.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
    simpa only [hz, Function.comp_def, Submodule.subtype_apply] using h
  obtain ⟨p,hp,hi⟩ := affine_independent_polynomial (fun i => f (z i))
    (fun i => g (z i)) hli
  refine ⟨p,hp,?_⟩
  intro t ht
  let ft : V →ₗ[K] W := (1-t) • f + t • g
  let bt : Fin (Module.finrank K (LinearMap.range f)) → LinearMap.range ft :=
    fun i => ⟨ft (z i), LinearMap.mem_range_self _ _⟩
  have htli : LinearIndependent K bt := by
    apply LinearIndependent.of_comp (LinearMap.range ft).subtype
    exact hi t ht
  have hb := htli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hb
  have hf := (LinearMap.range f).finrank_quotient_add_finrank
  have hg := (LinearMap.range ft).finrank_quotient_add_finrank
  dsimp only [ft] at hg hb
  omega

end AffineCokernel
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section GenericPieceBound
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]

theorem generic_homogeneous_quotient_bound (w : σ → G) (e : E → G)
    (F Q : E → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous w (e i))
    (hQ : ∀ i, (Q i).IsWeightedHomogeneous w (e i))
    (d : G) [Module.Finite K (Piece (K := K) w d)] :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ t : K, p.eval t ≠ 0 →
      Module.finrank K (componentQuotient w
        (Ideal.span (Set.range (fun i => (1-t) • Q i + t • F i))) d) ≤
      Module.finrank K (componentQuotient w (Ideal.span (Set.range Q)) d) := by
  obtain ⟨p,hp,h⟩ := affine_cokernel_polynomial
    (homogeneousIdealMap w e Q hQ d) (homogeneousIdealMap w e F hF d)
  refine ⟨p,hp,?_⟩
  intro t ht
  have h' := h t ht
  rw [← homogeneousIdealMap_affine w e F hF Q hQ d t] at h'
  rw [homogeneousIdealMap_range w e Q hQ d] at h'
  rw [homogeneousIdealMap_range] at h'
  exact h'

end GenericPieceBound

section ProductComparison
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem generic_product_piece_bound (a : ι →₀ ℕ)
    (qs : List (FactorPair (K := K) (blockWeight (fun v : BlockVariables a => v.1))))
    (u v : Fin qs.length → ι) (t : (Fin qs.length × Bool) → K)
    (ht : Function.Injective t)
    (hleft : ∀ i, (qs.get i).left = blockLinearForm a (u i) (t (i,false)))
    (hright : ∀ i, (qs.get i).right = blockLinearForm a (v i) (t (i,true)))
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1)
    (hlen : qs.length = ∑ j, a j)
    (F : Fin qs.length → MvPolynomial (BlockVariables a) K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      ((qs.get i).leftDegree + (qs.get i).rightDegree))
    (d : ι → ℤ) (hd : ∀ j, (qs.length : ℤ) < d j) :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ c : K, p.eval c ≠ 0 →
      pieceDim (blockWeight (fun v : BlockVariables a => v.1))
        (Ideal.span (Set.range (fun i =>
          (1-c) • ((qs.get i).left * (qs.get i).right) + c • F i))) d ≤
      (mixedPolynomial u v).coeff a := by
  let w := blockWeight (fun v : BlockVariables a => v.1)
  obtain ⟨p,hp,h⟩ := generic_homogeneous_quotient_bound w
    (fun i => (qs.get i).leftDegree + (qs.get i).rightDegree) F
    (fun i => (qs.get i).left * (qs.get i).right) hF
    (fun i => (qs.get i).left_homogeneous.mul (qs.get i).right_homogeneous) d
  refine ⟨p,hp,?_⟩
  intro c hc
  apply (h c hc).trans
  rw [← productIdeal_eq_span]
  exact comparison_piece_bound a qs u v t ht hleft hright hdeg hlen d hd

end ProductComparison
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section BlockInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]
variable (group : σ → ι) (base : ι → σ) (hbase : ∀ j, group (base j) = j)

include hbase in
omit [Fintype ι] in
lemma normalized_pair_separator (x y : σ → K) (hxy : x ≠ y)
    (hx : ∀ j, x (base j) = 1) (hy : ∀ j, y (base j) = 1) :
    ∃ (p : MvPolynomial σ K) (e : ι → ℤ),
      p.IsWeightedHomogeneous (blockWeight group) e ∧
      (∀ j, 0 ≤ e j ∧ e j ≤ 1) ∧ eval x p = 1 ∧ eval y p = 0 := by
  classical
  obtain ⟨v,hv⟩ := Function.ne_iff.mp hxy
  let p : MvPolynomial σ K := C ((x v-y v)⁻¹) * (X v - C (y v) * X (base (group v)))
  refine ⟨p, Pi.single (group v) 1, ?_, ?_, ?_, ?_⟩
  · apply IsWeightedHomogeneous.C_mul
    apply IsWeightedHomogeneous.sub
    · exact isWeightedHomogeneous_X _ _ _
    · simpa only [blockWeight, hbase] using
        (isWeightedHomogeneous_X K (blockWeight group) (base (group v))).C_mul (y v)
  · intro j; by_cases h : j = group v <;> simp [h]
  · simp [p, hx, sub_ne_zero.mpr hv]
  · simp [p, hy]

include hbase in
lemma normalized_padding_homogeneous (b : ι → ℕ) :
    (∏ j, (X (base j) : MvPolynomial σ K) ^ b j).IsWeightedHomogeneous
      (blockWeight group) (fun j => (b j : ℤ)) := by
  classical
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun j => (X (base j) : MvPolynomial σ K) ^ b j)
    (fun j => b j • Pi.single j (1 : ℤ)) (fun j _ => by
      convert (isWeightedHomogeneous_X K (blockWeight group) (base j)).pow (b j) using 1
      simp only [blockWeight, hbase])
  convert h using 1
  ext j
  simp [Pi.single_apply]

omit [DecidableEq ι] in
lemma normalized_padding_eval (b : ι → ℕ) (x : σ → K) (hx : ∀ j, x (base j) = 1) :
    eval x (∏ j, (X (base j) : MvPolynomial σ K) ^ b j) = 1 := by
  simp [hx]

variable [Fintype L] [DecidableEq L]

include hbase in

theorem normalized_interpolation (d : ι → ℤ) (hd : ∀ j, (Fintype.card L : ℤ) ≤ d j)
    (x : L → σ → K) (hx : Function.Injective x) (hb : ∀ i j, x i (base j) = 1) :
    ∃ p : L → Piece (K := K) (blockWeight group) d,
      ∀ i j, eval (x j) (p i).val = if j = i then 1 else 0 := by
  classical
  have hs (i j : L) : ∃ (p : MvPolynomial σ K) (e : ι → ℤ),
      p.IsWeightedHomogeneous (blockWeight group) e ∧
      (∀ l, 0 ≤ e l ∧ e l ≤ 1) ∧ eval (x i) p = 1 ∧ (i ≠ j → eval (x j) p = 0) := by
    by_cases hij : i = j
    · refine ⟨1,0,isWeightedHomogeneous_one _ _,?_,by simp,?_⟩
      · intro l; simp
      · exact fun h => (h hij).elim
    · obtain ⟨p,e,hp,he,hi,hj⟩ := normalized_pair_separator group base hbase
        (x i) (x j) (fun h => hij (hx h)) (hb i) (hb j)
      exact ⟨p,e,hp,he,hi,fun _ => hj⟩
  choose p e hp he hi hj using hs
  let E : L → ι → ℤ := fun i => ∑ j, e i j
  have hE (i : L) (l : ι) : E i l ≤ Fintype.card L := by
    dsimp [E]
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (he i j l).2)
  let b : L → ι → ℕ := fun i l => (d l - E i l).toNat
  have hbdeg (i : L) : (fun l => (b i l : ℤ)) = d-E i := by
    funext l
    exact Int.toNat_of_nonneg (sub_nonneg.mpr ((hE i l).trans (hd l)))
  let P : L → MvPolynomial σ K := fun i =>
    (∏ j, p i j) * ∏ l, X (base l) ^ b i l
  have hPhom (i : L) : (P i).IsWeightedHomogeneous (blockWeight group) d := by
    have hp' := IsWeightedHomogeneous.prod Finset.univ (p i) (e i) (fun j _ => hp i j)
    have hb' := normalized_padding_homogeneous (K := K) group base hbase (b i)
    rw [hbdeg] at hb'
    have h := hp'.mul hb'
    have hdeg : (∑ j, e i j) + (d - E i) = d := by
      dsimp [E]; abel
    rw [hdeg] at h
    exact h
  refine ⟨fun i => ⟨P i,hPhom i⟩,?_⟩
  intro i j
  change eval (x j) (P i) = _
  simp only [P, map_mul, map_prod, normalized_padding_eval base (b i) (x j) (hb j), mul_one]
  by_cases hij : j = i
  · subst j
    simp [hi]
  · rw [ite_eq_right hij]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (hj i j (Ne.symm hij))

end BlockInterpolation
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section NormalizedPointBound
variable {K σ ι L : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

theorem normalized_points_le_pieceDim (group : σ → ι) (base : ι → σ)
    (hbase : ∀ j, group (base j) = j) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℤ) (hd : ∀ j, (Fintype.card L : ℤ) ≤ d j)
    (x : L → σ → K) (hx : Function.Injective x) (hb : ∀ i j, x i (base j) = 1)
    (hz : ∀ i, ∀ p ∈ I, eval (x i) p = 0) :
    Fintype.card L ≤ Module.finrank K (componentQuotient (blockWeight group) I d) := by
  classical
  let P := Piece (K := K) (blockWeight group) d
  let S : Submodule K P := (I.restrictScalars K).comap P.subtype
  let ev : P →ₗ[K] (L → K) := LinearMap.pi fun i =>
    (aeval (x i)).toLinearMap.comp P.subtype
  have heval (p : P) (i : L) : ev p i = eval (x i) p.val := by
    simp [ev]
  have hker : S ≤ LinearMap.ker ev := by
    intro p hp
    apply LinearMap.mem_ker.mpr
    funext i
    rw [heval]
    exact hz i p.val hp
  let qev := S.liftQ ev hker
  obtain ⟨p,hp⟩ := normalized_interpolation group base hbase d hd x hx hb
  have hs : Function.Surjective qev := by
    intro y
    refine ⟨S.mkQ (∑ i, y i • p i), ?_⟩
    change ev (∑ i, y i • p i) = y
    apply _root_.funext
    intro j
    have hei (i : L) : ev (p i) j = if j = i then 1 else 0 :=
      (heval (p i) j).trans (hp i j)
    calc
      ev (∑ i, y i • p i) j = ∑ i, y i * ev (p i) j := by simp
      _ = y j := by simp [hei]
  have h := LinearMap.finrank_le_finrank_of_surjective hs
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] using h

end NormalizedPointBound
end PermanentBorder.Multigraded

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Persistence
variable {C V : Type*}
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

def SimpleAt (F : C × V → V) (c : C) (x : V) : Prop :=
  (fderiv ℂ F (c,x) ∘L ContinuousLinearMap.inr ℂ C V).IsInvertible

theorem isInvertible_iff_isUnit (T : V →L[ℂ] V) : T.IsInvertible ↔ IsUnit T := by
  constructor
  · intro h
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr h.bijective
  · intro h
    obtain ⟨U,hU⟩ := h
    exact ⟨ContinuousLinearEquiv.ofUnit U, hU⟩

omit [CompleteSpace C] in

theorem isOpen_simple {F : C × V → V} (hF : ContDiff ℂ 1 F) :
    IsOpen {u : C × V | SimpleAt F u.1 u.2} := by
  have hc : Continuous (fun u : C × V =>
      fderiv ℂ F u ∘L ContinuousLinearMap.inr ℂ C V) := by
    exact (hF.continuous_fderiv (by decide)).clm_comp continuous_const
  simpa only [SimpleAt, Prod.mk.eta, isInvertible_iff_isUnit, Set.preimage_ofPred_eq] using
    Units.isOpen.preimage hc

theorem simple_branch {F : C × V → V} (hF : ContDiff ℂ 1 F)
    {c : C} {x : V} (hz : F (c,x) = 0) (hs : SimpleAt F c x) :
    ∃ ψ : C → V, Tendsto ψ (𝓝 c) (𝓝 x) ∧
      ∀ᶠ c' in 𝓝 c, F (c', ψ c') = 0 ∧ SimpleAt F c' (ψ c') := by
  let hf := hF.contDiffAt (x := (c,x))
  let ψ := hf.implicitFunction (by decide) hs
  have ht : Tendsto ψ (𝓝 c) (𝓝 x) :=
    hf.hasStrictFDerivAt (by decide) |>.tendsto_implicitFunctionOfProdDomain hs
  refine ⟨ψ,ht,?_⟩
  have hz' := hf.eventually_apply_implicitFunction (by decide) hs
  have hne := (tendsto_id.prodMk_nhds ht).eventually ((isOpen_simple hF).mem_nhds hs)
  filter_upwards [hz', hne] with c' hc' hs'
  exact ⟨hc'.trans hz, hs'⟩

theorem finite_simple_zeros_persist {ι : Type*} [Fintype ι]
    {F : C × V → V} (hF : ContDiff ℂ 1 F) {c : C}
    (x : ι → V) (hx : Function.Injective x)
    (hz : ∀ i, F (c,x i) = 0) (hs : ∀ i, SimpleAt F c (x i)) :
    ∀ᶠ c' in 𝓝 c, ∃ y : ι → V, Function.Injective y ∧
      ∀ i, F (c',y i) = 0 ∧ SimpleAt F c' (y i) := by
  classical
  choose ψ ht hψ using fun i => simple_branch hF (hz i) (hs i)
  have hall : ∀ᶠ c' in 𝓝 c, ∀ i, F (c',ψ i c') = 0 ∧ SimpleAt F c' (ψ i c') :=
    Filter.eventually_all.mpr hψ
  have hsep : ∀ᶠ c' in 𝓝 c, Function.Injective (fun i => ψ i c') := by
    have hp : ∀ i j : ι, ∀ᶠ c' in 𝓝 c, i ≠ j → ψ i c' ≠ ψ j c' := by
      intro i j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall (by simp [hij])
      · have hh : (x i, x j) ∈ {p : V × V | p.1 ≠ p.2} := by
          exact fun h => hij (hx h)
        have ho : IsOpen {p : V × V | p.1 ≠ p.2} := isOpen_compl_iff.mpr (isClosed_eq continuous_fst continuous_snd)
        have he := ((ht i).prodMk_nhds (ht j)).eventually (ho.mem_nhds hh)
        exact he.mono fun _ h _ => h
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hp i))] with c' hc'
    intro i j he
    by_contra hij
    exact hc' i j hij he
  filter_upwards [hall,hsep] with c' hc' hi
  exact ⟨fun i => ψ i c',hi,hc'⟩
end Persistence
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
theorem fderiv_slice {C V : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    {F : C × V → V} (hF : ContDiff ℂ 1 F) (c : C) (x : V) :
    fderiv ℂ (fun x => F (c,x)) x =
      fderiv ℂ F (c,x) ∘L ContinuousLinearMap.inr ℂ C V := by
  have hi : HasFDerivAt (fun x : V => (c,x)) (ContinuousLinearMap.inr ℂ C V) x := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const (𝕜 := ℂ) c x).prodMk (hasFDerivAt_id (𝕜 := ℂ) x)
  exact ((hF.differentiable (by decide) (c,x)).hasFDerivAt.comp x hi).fderiv

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open MvPolynomial
variable {τ : Type*} [Fintype τ]
theorem contDiff_mvPolynomial_eval (p : MvPolynomial τ ℂ) :
    ContDiff ℂ 1 (fun x : τ → ℂ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℂ 1 (fun _ : τ → ℂ => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℂ ℂ i)

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section ProductSimplePointBound
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

theorem product_simple_point_bound_chart (a : ι →₀ ℕ)
    (qs : List (FactorPair (K := ℂ) (blockWeight (fun v : BlockVariables a => v.1))))
    (u v : Fin qs.length → ι) (t : (Fin qs.length × Bool) → ℂ)
    (ht : Function.Injective t)
    (hleft : ∀ i, (qs.get i).left = blockLinearForm a (u i) (t (i,false)))
    (hright : ∀ i, (qs.get i).right = blockLinearForm a (v i) (t (i,true)))
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1)
    (hlen : qs.length = ∑ j, a j)
    (F : Fin qs.length → MvPolynomial (BlockVariables a) ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      ((qs.get i).leftDegree + (qs.get i).rightDegree))
    (base : ι → BlockVariables a) (hbase : ∀ j, (base j).1 = j)
    (chart : (Fin qs.length → ℂ) → BlockVariables a → ℂ)
    (hc : ContDiff ℂ 1 chart) (hci : Function.Injective chart)
    (hcn : ∀ z j, chart z (base j) = 1)
    (x : L → Fin qs.length → ℂ) (hx : Function.Injective x)
    (hz : ∀ i j, eval (chart (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z j => eval (chart z) (F j)) (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let Q : Fin qs.length → MvPolynomial (BlockVariables a) ℂ :=
    fun i => (qs.get i).left * (qs.get i).right
  let family : ℂ × (Fin qs.length → ℂ) → Fin qs.length → ℂ :=
    fun z i => (1-z.1) * eval (chart z.2) (Q i) + z.1 * eval (chart z.2) (F i)
  have hcont : ContDiff ℂ 1 family := by
    apply contDiff_pi.mpr
    intro i
    exact ((contDiff_const.sub contDiff_fst).mul
      ((PolarAnalysis.contDiff_mvPolynomial_eval (Q i)).comp (hc.comp contDiff_snd))).add
      (contDiff_fst.mul
        ((PolarAnalysis.contDiff_mvPolynomial_eval (F i)).comp (hc.comp contDiff_snd)))
  have hone : (fun z => family (1,z)) = (fun z j => eval (chart z) (F j)) := by
    funext z j
    simp [family]
  have hzero (i : L) : family (1,x i) = 0 := by
    rw [congrFun hone]
    funext j
    exact hz i j
  have hsimple (i : L) : PolarAnalysis.SimpleAt family 1 (x i) := by
    unfold PolarAnalysis.SimpleAt
    rw [← PolarAnalysis.fderiv_slice hcont, hone]
    exact hs i
  have hpersist := PolarAnalysis.finite_simple_zeros_persist hcont x hx hzero hsimple
  let d : ι → ℤ := fun _ => qs.length + Fintype.card L + 1
  obtain ⟨p,hp,hbound⟩ := generic_product_piece_bound a qs u v t ht hleft hright hdeg
    hlen F hF d (by intro j; dsimp [d]; omega)
  have hpne : p ≠ 0 := by
    intro h
    rw [h, Polynomial.eval_zero] at hp
    exact zero_ne_one hp
  have hdense : Dense {c : ℂ | p.eval c ≠ 0} := by
    exact (Polynomial.finite_setOfPred_isRoot hpne).countable.dense_compl ℂ
  obtain ⟨c,hpc,y,hy,hyz⟩ := hdense.inter_nhds_nonempty hpersist
  let I := Ideal.span (Set.range (fun i => (1-c) • Q i + c • F i))
  have hyideal (i : L) : ∀ p ∈ I, eval (chart (y i)) p = 0 := by
    have hI : I ≤ RingHom.ker (eval (chart (y i))) := by
      apply Ideal.span_le.mpr
      rintro p ⟨j,rfl⟩
      change eval (chart (y i)) ((1-c) • Q j + c • F j) = 0
      have h := congrFun (hyz i).1 j
      simpa only [family, map_add, smul_eval, Pi.zero_apply] using h
    exact fun p hp => hI hp
  have hpoints := normalized_points_le_pieceDim (fun v : BlockVariables a => v.1)
    base hbase I d (by intro j; dsimp [d]; omega) (fun i => chart (y i)) (hci.comp hy)
    (fun i j => hcn (y i) j) hyideal
  exact hpoints.trans (hbound c hpc)

end ProductSimplePointBound
end PermanentBorder.Multigraded

end OAI
