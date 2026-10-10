import OAI.Algebra.Determinantal.PointBounds

namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearPointCount
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

noncomputable def vandermondePairs (a : ι →₀ ℕ) {M : ℕ}
    (u v : Fin M → ι) (t : (Fin M × Bool) → ℂ) :
    Fin M → FactorPair (K := ℂ) (blockWeight (fun v : BlockVariables a => v.1)) :=
  fun i => { left := blockLinearForm a (u i) (t (i,false))
             right := blockLinearForm a (v i) (t (i,true))
             leftDegree := Pi.single (u i) 1
             rightDegree := Pi.single (v i) 1
             left_homogeneous := blockLinearForm_homogeneous a (u i) (t (i,false))
             right_homogeneous := blockLinearForm_homogeneous a (v i) (t (i,true)) }

theorem bilinear_simple_point_count_chart (a : ι →₀ ℕ) {M : ℕ}
    (u v : Fin M → ι) (hM : M = ∑ j, a j)
    (F : Fin M → MvPolynomial (BlockVariables a) ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      (Pi.single (u i) 1 + Pi.single (v i) 1))
    (base : ι → BlockVariables a) (hbase : ∀ j, (base j).1 = j)
    (chart : (Fin M → ℂ) → BlockVariables a → ℂ)
    (hc : ContDiff ℂ 1 chart) (hci : Function.Injective chart)
    (hcn : ∀ z j, chart z (base j) = 1)
    (x : L → Fin M → ℂ) (hx : Function.Injective x)
    (hz : ∀ i j, eval (chart (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z j => eval (chart z) (F j)) (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let t : (Fin M × Bool) → ℂ := fun i =>
    Infinite.natEmbedding ℂ ((Fintype.equivFin (Fin M × Bool) i).val)
  have ht : Function.Injective t :=
    (Infinite.natEmbedding ℂ).injective.comp
      (Fin.val_injective.comp (Fintype.equivFin (Fin M × Bool)).injective)
  generalize hqs : List.ofFn (vandermondePairs a u v t) = qs
  have hlen : qs.length = M := by rw [← hqs, List.length_ofFn]
  cases hlen
  have hget (i : Fin qs.length) : qs.get i = vandermondePairs a u v t i := by
    have h := congrArg (fun l => l[i.val]?) hqs
    simpa only [List.getElem?_ofFn, dite_eq_left i.isLt, List.getElem?_eq_getElem i.isLt,
      Option.some.injEq, List.get_eq_getElem] using h.symm
  apply product_simple_point_bound_chart a qs u v t ht
    (fun i => by rw [hget]; rfl) (fun i => by rw [hget]; rfl) ?_ hM F
    (by intro i; simpa only [hget, vandermondePairs] using hF i)
    base hbase chart hc hci hcn x hx hz hs
  intro q hq j
  rw [← hqs] at hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  by_cases hj : j = u i <;> simp [vandermondePairs, hj]

end BilinearPointCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProductAffineChart
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev BlockAffineVariables (a : ι → ℕ) := (j : ι) × Fin (a j)

noncomputable def productAffineChart (a : ι → ℕ) {M : ℕ}
    (e : BlockAffineVariables a ≃ Fin M) (z : Fin M → ℂ) : BlockVariables a → ℂ :=
  fun v => Fin.cases 1 (fun q => z (e ⟨v.1,q⟩)) v.2

omit [Fintype ι] [DecidableEq ι] in
lemma productAffineChart_zero (a : ι → ℕ) {M : ℕ}
    (e : BlockAffineVariables a ≃ Fin M) (z : Fin M → ℂ) (j : ι) :
    productAffineChart a e z ⟨j,0⟩ = 1 := by
  simp [productAffineChart]

omit [Fintype ι] [DecidableEq ι] in
lemma productAffineChart_succ (a : ι → ℕ) {M : ℕ}
    (e : BlockAffineVariables a ≃ Fin M) (z : Fin M → ℂ) (j : ι) (q : Fin (a j)) :
    productAffineChart a e z ⟨j,q.succ⟩ = z (e ⟨j,q⟩) := by
  simp [productAffineChart]

omit [Fintype ι] [DecidableEq ι] in
lemma productAffineChart_injective (a : ι → ℕ) {M : ℕ}
    (e : BlockAffineVariables a ≃ Fin M) : Function.Injective (productAffineChart a e) := by
  intro z z' h
  funext i
  obtain ⟨⟨j,q⟩,rfl⟩ := e.surjective i
  have h := congrFun h ⟨j,q.succ⟩
  simpa only [productAffineChart_succ] using h

omit [DecidableEq ι] in
lemma productAffineChart_contDiff (a : ι → ℕ) {M : ℕ}
    (e : BlockAffineVariables a ≃ Fin M) : ContDiff ℂ 1 (productAffineChart a e) := by
  apply contDiff_pi.mpr
  rintro ⟨j,q⟩
  refine Fin.cases ?_ (fun q => ?_) q
  · simpa only [productAffineChart_zero] using
      (contDiff_const : ContDiff ℂ 1 (fun _ : Fin M → ℂ => (1 : ℂ)))
  · simpa only [productAffineChart_succ] using contDiff_apply ℂ ℂ (e ⟨j,q⟩)

variable {L : Type*} [Fintype L] [DecidableEq L]

theorem bilinear_simple_point_count (a : ι →₀ ℕ) {M : ℕ}
    (e : BlockAffineVariables a ≃ Fin M) (u v : Fin M → ι)
    (F : Fin M → MvPolynomial (BlockVariables a) ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      (Pi.single (u i) 1 + Pi.single (v i) 1))
    (x : L → Fin M → ℂ) (hx : Function.Injective x)
    (hz : ∀ i j, eval (productAffineChart a e (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z j => eval (productAffineChart a e z) (F j))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  have hM : M = ∑ j, a j := by
    have h := Fintype.card_congr e
    simpa only [BlockAffineVariables, Fintype.card_sigma, Fintype.card_fin] using h.symm
  exact bilinear_simple_point_count_chart a u v hM F hF (fun j => ⟨j,0⟩) (fun _ => rfl)
    (productAffineChart a e) (productAffineChart_contDiff a e)
    (productAffineChart_injective a e) (productAffineChart_zero a e) x hx hz hs

end ProductAffineChart
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectiveInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]

def BlockSeparated (group : σ → ι) (x y : σ → K) : Prop :=
  ∃ v w, group v = group w ∧ x v * y w ≠ x w * y v

omit [Fintype ι] in
lemma projective_pair_separator (group : σ → ι) (x y : σ → K)
    (hxy : BlockSeparated group x y) :
    ∃ (p : MvPolynomial σ K) (e : ι → ℤ),
      p.IsWeightedHomogeneous (blockWeight group) e ∧
      (∀ j, 0 ≤ e j ∧ e j ≤ 1) ∧ eval x p = 1 ∧ eval y p = 0 := by
  classical
  obtain ⟨v,w,hvw,hxy⟩ := hxy
  let p : MvPolynomial σ K := C ((x v * y w - x w * y v)⁻¹) *
    (C (y w) * X v - C (y v) * X w)
  refine ⟨p, Pi.single (group v) 1, ?_, ?_, ?_, ?_⟩
  · apply IsWeightedHomogeneous.C_mul
    apply IsWeightedHomogeneous.sub
    · exact (isWeightedHomogeneous_X K (blockWeight group) v).C_mul _
    · simpa only [blockWeight, hvw] using
        (isWeightedHomogeneous_X K (blockWeight group) w).C_mul (y v)
  · intro j; by_cases h : j = group v <;> simp [h]
  · simp only [p, map_mul, eval_C, map_sub, eval_X]
    rw [mul_comm (y w), mul_comm (y v), inv_mul_cancel₀ (sub_ne_zero.mpr hxy)]
  · simp [p, mul_comm]

variable [Fintype L] [DecidableEq L]

theorem projective_interpolation (group : σ → ι) (d : ι → ℤ)
    (hd : ∀ j, (Fintype.card L : ℤ) ≤ d j)
    (x : L → σ → K) (hx : ∀ i j, i ≠ j → BlockSeparated group (x i) (x j))
    (base : L → ι → σ) (hbase : ∀ i j, group (base i j) = j)
    (hb : ∀ i j, x i (base i j) ≠ 0) :
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
    · obtain ⟨p,e,hp,he,hi,hj⟩ := projective_pair_separator group (x i) (x j) (hx i j hij)
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
  let pad : L → MvPolynomial σ K := fun i =>
    ∏ l, (C ((x i (base i l))⁻¹) * X (base i l)) ^ b i l
  have hpadhom (i : L) : (pad i).IsWeightedHomogeneous (blockWeight group) (d - E i) := by
    rw [← hbdeg]
    have h := IsWeightedHomogeneous.prod Finset.univ
      (fun l => (C ((x i (base i l))⁻¹) * X (base i l) : MvPolynomial σ K)^b i l)
      (fun l => b i l • Pi.single l (1 : ℤ)) (fun l _ => by
        convert ((isWeightedHomogeneous_X K (blockWeight group) (base i l)).C_mul
          ((x i (base i l))⁻¹)).pow (b i l) using 1
        simp only [blockWeight, hbase])
    convert h using 1
    ext l
    simp [Pi.single_apply]
  have hpadeval (i : L) : eval (x i) (pad i) = 1 := by
    simp [pad, inv_mul_cancel₀ (hb i _)]
  let P : L → MvPolynomial σ K := fun i => (∏ j, p i j) * pad i
  have hPhom (i : L) : (P i).IsWeightedHomogeneous (blockWeight group) d := by
    have hp' := IsWeightedHomogeneous.prod Finset.univ (p i) (e i) (fun j _ => hp i j)
    have h := hp'.mul (hpadhom i)
    have hdeg : (∑ j, e i j) + (d - E i) = d := by dsimp [E]; abel
    rw [hdeg] at h
    exact h
  refine ⟨fun i => ⟨P i,hPhom i⟩,?_⟩
  intro i j
  change eval (x j) (P i) = _
  simp only [P, map_mul, map_prod]
  by_cases hij : j = i
  · subst j
    simp [hi, hpadeval]
  · rw [ite_eq_right hij, Finset.prod_eq_zero (Finset.mem_univ j) (hj i j (Ne.symm hij)), zero_mul]

end ProjectiveInterpolation
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectivePointBound
variable {K σ ι L : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

theorem projective_points_le_pieceDim (group : σ → ι) (base : L → ι → σ)
    (hbase : ∀ i j, group (base i j) = j) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℤ) (hd : ∀ j, (Fintype.card L : ℤ) ≤ d j)
    (x : L → σ → K) (hx : ∀ i j, i ≠ j → BlockSeparated group (x i) (x j))
    (hb : ∀ i j, x i (base i j) ≠ 0)
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
  obtain ⟨p,hp⟩ := projective_interpolation group d hd x hx base hbase hb
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

end ProjectivePointBound
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section MultiChartProductCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

omit [Fintype ι] [DecidableEq ι] in

lemma eventually_blockSeparated {σ : Type*} (group : σ → ι)
    (x : L → σ → ℂ) (hx : ∀ i j, i ≠ j → BlockSeparated group (x i) (x j))
    {y : L → ℂ → σ → ℂ} {c : ℂ}
    (hy : ∀ i, Tendsto (y i) (𝓝 c) (𝓝 (x i))) :
    ∀ᶠ c' in 𝓝 c, ∀ i j, i ≠ j → BlockSeparated group (y i c') (y j c') := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
  obtain ⟨v,w,hvw,hn⟩ := hx i j hij
  have hv₁ := (continuous_apply v).tendsto (x i) |>.comp (hy i)
  have hw₁ := (continuous_apply w).tendsto (x i) |>.comp (hy i)
  have hv₂ := (continuous_apply v).tendsto (x j) |>.comp (hy j)
  have hw₂ := (continuous_apply w).tendsto (x j) |>.comp (hy j)
  have he := ((hv₁.mul hw₂).sub (hw₁.mul hv₂)).eventually_ne (sub_ne_zero.mpr hn)
  exact he.mono (fun c' hc' _ => ⟨v,w,hvw,sub_ne_zero.mp hc'⟩)

theorem product_simple_point_bound_multichart (a : ι →₀ ℕ)
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
    (base : L → ι → BlockVariables a) (hbase : ∀ i j, (base i j).1 = j)
    (e : L → (Fin qs.length → ℂ) ≃L[ℂ] V)
    (chart : L → V → BlockVariables a → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
      (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let Q : Fin qs.length → MvPolynomial (BlockVariables a) ℂ :=
    fun j => (qs.get j).left * (qs.get j).right
  let family : L → ℂ × V → V := fun i z => e i
    (fun j => (1-z.1) * eval (chart i z.2) (Q j) + z.1 * eval (chart i z.2) (F j))
  have hcont (i : L) : ContDiff ℂ 1 (family i) := by
    apply (e i).contDiff.comp
    apply contDiff_pi.mpr
    intro j
    exact ((contDiff_const.sub contDiff_fst).mul
      ((PolarAnalysis.contDiff_mvPolynomial_eval (Q j)).comp ((hc i).comp contDiff_snd))).add
      (contDiff_fst.mul
        ((PolarAnalysis.contDiff_mvPolynomial_eval (F j)).comp ((hc i).comp contDiff_snd)))
  have hone (i : L) : (fun z => family i (1,z)) =
      (fun z => e i (fun j => eval (chart i z) (F j))) := by
    funext z
    simp [family]
  have hzero (i : L) : family i (1,x i) = 0 := by
    rw [congrFun (hone i)]
    rw [show (fun j => eval (chart i (x i)) (F j)) = 0 from funext (hz i), map_zero]
  have hsimple (i : L) : PolarAnalysis.SimpleAt (family i) 1 (x i) := by
    unfold PolarAnalysis.SimpleAt
    rw [← PolarAnalysis.fderiv_slice (hcont i), hone]
    exact hs i
  choose ψ hψ hzψ using fun i => PolarAnalysis.simple_branch (hcont i) (hzero i) (hsimple i)
  have hsep := eventually_blockSeparated (fun v : BlockVariables a => v.1)
    (fun i => chart i (x i)) hx (fun i => (hc i).continuous.continuousAt.tendsto.comp (hψ i))
  have hpersist : ∀ᶠ c in 𝓝 (1 : ℂ),
      (∀ i, family i (c,ψ i c) = 0) ∧
      ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
        (chart i (ψ i c)) (chart j (ψ j c)) := by
    filter_upwards [Filter.eventually_all.mpr hzψ, hsep] with c hz hc
    exact ⟨fun i => (hz i).1,hc⟩
  let d : ι → ℤ := fun _ => qs.length + Fintype.card L + 1
  obtain ⟨p,hp,hbound⟩ := generic_product_piece_bound a qs u v t ht hleft hright hdeg
    hlen F hF d (by intro j; dsimp [d]; omega)
  have hpne : p ≠ 0 := by
    intro h
    rw [h, Polynomial.eval_zero] at hp
    exact zero_ne_one hp
  have hdense : Dense {c : ℂ | p.eval c ≠ 0} :=
    (Polynomial.finite_setOfPred_isRoot hpne).countable.dense_compl ℂ
  obtain ⟨c,hpc,hyz,hy⟩ := hdense.inter_nhds_nonempty hpersist
  let I := Ideal.span (Set.range (fun j => (1-c) • Q j + c • F j))
  have hyideal (i : L) : ∀ p ∈ I, eval (chart i (ψ i c)) p = 0 := by
    have hI : I ≤ RingHom.ker (eval (chart i (ψ i c))) := by
      apply Ideal.span_le.mpr
      rintro p ⟨j,rfl⟩
      change eval (chart i (ψ i c)) ((1-c) • Q j + c • F j) = 0
      have h := (e i).injective ((hyz i).trans (map_zero (e i)).symm)
      have h := congrFun h j
      simpa only [map_add, smul_eval, Pi.zero_apply] using h
    exact fun p hp => hI hp
  have hpoints := projective_points_le_pieceDim (fun v : BlockVariables a => v.1)
    base hbase I d (by intro j; dsimp [d]; omega) (fun i => chart i (ψ i c)) hy
    (fun i j => by rw [hcn]; exact one_ne_zero) hyideal
  exact hpoints.trans (hbound c hpc)

end MultiChartProductCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearMultiChartCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem bilinear_simple_point_count_multichart (a : ι →₀ ℕ) {M : ℕ}
    (u v : Fin M → ι) (hM : M = ∑ j, a j)
    (F : Fin M → MvPolynomial (BlockVariables a) ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      (Pi.single (u i) 1 + Pi.single (v i) 1))
    (base : L → ι → BlockVariables a) (hbase : ∀ i j, (base i j).1 = j)
    (e : L → (Fin M → ℂ) ≃L[ℂ] V)
    (chart : L → V → BlockVariables a → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
      (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let t : (Fin M × Bool) → ℂ := fun i =>
    Infinite.natEmbedding ℂ ((Fintype.equivFin (Fin M × Bool) i).val)
  have ht : Function.Injective t :=
    (Infinite.natEmbedding ℂ).injective.comp
      (Fin.val_injective.comp (Fintype.equivFin (Fin M × Bool)).injective)
  generalize hqs : List.ofFn (vandermondePairs a u v t) = qs
  have hlen : qs.length = M := by rw [← hqs, List.length_ofFn]
  cases hlen
  have hget (i : Fin qs.length) : qs.get i = vandermondePairs a u v t i := by
    have h := congrArg (fun l => l[i.val]?) hqs
    simpa only [List.getElem?_ofFn, dite_eq_left i.isLt, List.getElem?_eq_getElem i.isLt,
      Option.some.injEq, List.get_eq_getElem] using h.symm
  apply product_simple_point_bound_multichart a qs u v t ht
    (fun i => by rw [hget]; rfl) (fun i => by rw [hget]; rfl) ?_ hM F
    (by intro i; simpa only [hget, vandermondePairs] using hF i)
    base hbase e chart hc hcn x hx hz hs
  intro q hq j
  rw [← hqs] at hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  by_cases hj : j = u i <;> simp [vandermondePairs, hj]

end BilinearMultiChartCount
end PermanentBorder.Multigraded

end OAI
