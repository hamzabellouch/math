import OAI.Analysis.Mahler.Lens
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Filter Finset Metric
open scoped Topology

lemma mem_convexHull_zero_fiber {P E : Type*}
    [AddCommGroup E] [Module ℝ E] {S : Set P}
    (f : P → E) (g : P → ℝ) (hg : ∀ p ∈ S, 0 ≤ g p) {e : E}
    (he : (e, (0:ℝ)) ∈ convexHull ℝ ((fun p => (f p, g p)) '' S)) :
    e ∈ convexHull ℝ (f '' {p ∈ S | g p = 0}) := by
  classical
  obtain ⟨ι,_,z,w,hz,_,hw,hs,heq⟩ := eq_pos_convex_span_of_mem_convexHull he
  have hz' (i : ι) := hz (mem_range_self i)
  choose p hp hpeq using hz'
  have hsumg : ∑ i, w i * g (p i) = 0 := by
    have h := congrArg Prod.snd heq
    simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul, ← hpeq] using h
  have hg0 (i : ι) : g (p i) = 0 := by
    have hh := (sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hw j).le (hg _ (hp j)))).mp hsumg i (mem_univ i)
    exact (mul_eq_zero.mp hh).resolve_left (hw i).ne'
  have heqf : ∑ i, w i • f (p i) = e := by
    have h := congrArg Prod.fst heq
    simpa only [Prod.fst_sum, Prod.smul_fst, ← hpeq] using h
  exact mem_convexHull_of_exists_fintype w (fun i => f (p i)) (fun i => (hw i).le) hs
    (fun i => ⟨p i,⟨hp i,hg0 i⟩,rfl⟩) heqf

lemma isCompact_convexHull_of_isCompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  classical
  let D := Module.finrank ℝ E + 1
  let T (k : ℕ) : Set ((Fin k → ℝ) × (Fin k → E)) :=
    {weights : Fin k → ℝ | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1} ×ˢ
      Set.pi Set.univ (fun _ => S)
  let f (k : ℕ) (p : (Fin k → ℝ) × (Fin k → E)) := ∑ i, p.1 i • p.2 i
  have hWeights (k : ℕ) :
      IsCompact {weights : Fin k → ℝ | (∀ index, 0 ≤ weights index) ∧
        ∑ index, weights index = 1} := by
    have compact := isCompact_range
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin k)).continuous
    rw [Convexity.StdSimplex.range_toFun_comp_weights] at compact
    simpa only [Set.iInter_ofPred, Set.ofPred_inter_eq_sep, Set.mem_ofPred_eq,
      and_comm] using compact
  have hT (k : ℕ) : IsCompact (T k) :=
    (hWeights k).prod (by
      convert (isCompact_pi_infinite (ι := Fin k) (fun _ => hS)) using 1
      ext x
      simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq])
  have hf (k : ℕ) : Continuous (f k) := by unfold f; fun_prop
  have he : convexHull ℝ S = ⋃ k : Fin (D+1), f k '' T k := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨ι,_,z,w,hz,hind,hw,hs,hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      let e := Fintype.equivFin ι
      have hk : Fintype.card ι < D+1 := by
        have hh := hind.card_le_finrank_succ
        have hb := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
        dsimp [D]
        omega
      apply Set.mem_iUnion.mpr
      refine ⟨⟨Fintype.card ι,hk⟩, (w ∘ e.symm,z ∘ e.symm), ?_, ?_⟩
      · refine ⟨⟨fun i => (hw (e.symm i)).le, ?_⟩, ?_⟩
        · simpa only [Function.comp_apply, Equiv.sum_comp] using hs
        · intro i hi
          exact hz (mem_range_self _)
      · dsimp only [f,Function.comp_apply]
        exact (e.symm.sum_comp (fun i => w i • z i)).trans hx
    · intro x hx
      obtain ⟨k,p, hp, rfl⟩ := Set.mem_iUnion.mp hx
      exact mem_convexHull_of_exists_fintype p.1 p.2 hp.1.1 hp.1.2
        (fun i => hp.2 i (Set.mem_univ i)) rfl
  rw [he]
  exact isCompact_iUnion (fun k => (hT k).image (hf k))

lemma mem_convexHull_zero_fiber_of_tendsto {P E : Type*}
    [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set P} (hS : IsCompact S)
    (f : P → E) (g : P → ℝ) (hf : ContinuousOn f S) (hgc : ContinuousOn g S)
    (hg : ∀ p ∈ S, 0 ≤ g p)
    (v : ℕ → E) (c : ℕ → ℝ)
    (hv : ∀ j, (v j,c j) ∈ convexHull ℝ ((fun p => (f p,g p)) '' S))
    {e : E} (hve : Tendsto v atTop (𝓝 e)) (hcz : Tendsto c atTop (𝓝 0)) :
    e ∈ convexHull ℝ (f '' {p ∈ S | g p = 0}) := by
  apply mem_convexHull_zero_fiber f g hg
  have hc := isCompact_convexHull_of_isCompact (hS.image_of_continuousOn (hf.prodMk hgc))
  exact hc.isClosed.mem_of_tendsto (hve.prodMk_nhds hcz) (Eventually.of_forall hv)

lemma pow_mul_one_sub_le_inv {t : ℝ} (ht : t ∈ Set.Icc 0 1) (k : ℕ) :
    t^k * (1-t) ≤ 1 / ((k:ℝ)+1) := by
  have hp (i : ℕ) (hi : i ∈ range (k+1)) : t^k ≤ t^i :=
    pow_le_pow_of_le_one ht.1 ht.2 (by have hh := Finset.mem_range.mp hi; omega)
  have hsum : ((k:ℝ)+1)*t^k ≤ ∑ i ∈ range (k+1), t^i := by
    simpa only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using
      sum_le_sum (fun i hi => hp i hi)
  have hmul := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr ht.2)
  have hgeo : (∑ i ∈ range (k+1), t^i) * (1-t) = 1-t^(k+1) := by
    exact geom_sum_mul_neg t (k+1)
  rw [hgeo] at hmul
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [pow_nonneg ht.1 (k+1)]

open Set Filter Finset Metric Complex
open scoped Topology
open MahlerConformal

def rowPair {n : ℕ} (h x : Fin n → ℝ) : ℝ := ∑ i, h i*x i

lemma continuous_rowPair {n : ℕ} :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => rowPair p.1 p.2) := by
  unfold rowPair
  fun_prop

def rowComplex {n : ℕ} (h : Fin n → ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℂ :=
  (rowPair h z.1 : ℂ) + (rowPair h z.2 : ℂ)*I

lemma continuous_rowComplex {n : ℕ} :
    Continuous (fun p : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      rowComplex p.1 p.2) := by
  unfold rowComplex rowPair
  fun_prop

theorem common_boundary_witness_of_concentration {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC : IsCompact C)
    {Z : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hZ : IsCompact Z)
    (J : ℕ → Type) [∀ j, Fintype (J j)]
    (z : ℕ → ((Fin n → ℝ) × (Fin n → ℝ))) (hz : ∀ j, z j ∈ Z)
    (h : ∀ j, J j → Fin n → ℝ) (w : ∀ j, J j → ℝ) (ζ : ∀ j, J j → ℂ)
    (hh : ∀ j i, h j i ∈ C) (hw : ∀ j i, 0 ≤ w j i)
    (hs : ∀ j, ∑ i, w j i = 1)
    (hd : ∀ j i, ‖ζ j i‖ ≤ 1)
    (hF : ∀ j i, F (ζ j i) = rowComplex (h j i) (z j))
    (hy : ∀ j i, 0 ≤ rowPair (h j i) (z j).2)
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hz₀ : Tendsto z atTop (𝓝 z₀))
    {e : Fin n → ℝ} (he : Tendsto (fun j => ∑ i, w j i • h j i) atTop (𝓝 e))
    (hdef : Tendsto (fun j => ∑ i, w j i * (1-‖ζ j i‖)) atTop (𝓝 0)) :
    e ∈ convexHull ℝ {a ∈ C | rowPair a z₀.2 = lensWidth (rowPair a z₀.1)} := by
  classical
  let P : Type := C × (closedBall (0:ℂ) 1) × Z
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : CompactSpace (closedBall (0:ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  let f : P → (Fin n → ℝ) := fun p => p.1.val
  let g : P → ℝ := fun p => (1-‖p.2.1.val‖) +
    ‖F p.2.1.val - rowComplex p.1.val p.2.2.val‖ +
    max 0 (-rowPair p.1.val p.2.2.val.2) + ‖p.2.2.val-z₀‖
  have hc : Continuous (fun p : P => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hdisk : Continuous (fun p : P => p.2.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hzz : Continuous (fun p : P => p.2.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hf : Continuous f := hc
  have hcF : Continuous (fun p : P => F p.2.1.val) :=
    continuousOn_F_closed.comp_continuous hdisk (fun p => p.2.1.property)
  have hg : Continuous g :=
    (((continuous_const.sub hdisk.norm).add
      (hcF.sub (continuous_rowComplex.comp (hc.prodMk hzz))).norm).add
      (continuous_const.max ((continuous_rowPair.comp (hc.prodMk hzz.snd)).neg))).add
      (hzz.sub continuous_const).norm
  have hgn (p : P) : 0 ≤ g p := by
    dsimp only [g]
    exact add_nonneg (add_nonneg
      (add_nonneg (sub_nonneg.mpr (mem_closedBall_zero_iff.mp p.2.1.property))
        (norm_nonneg _)) (le_max_left _ _)) (norm_nonneg _)
  let p (j : ℕ) (i : J j) : P :=
    (⟨h j i,hh j i⟩,⟨ζ j i,mem_closedBall_zero_iff.mpr (hd j i)⟩,⟨z j,hz j⟩)
  have hgp (j : ℕ) (i : J j) :
      g (p j i) = (1-‖ζ j i‖) + ‖z j-z₀‖ := by
    simp only [g,p,hF j i,sub_self,norm_zero,add_zero,
      max_eq_left (neg_nonpos.mpr (hy j i))]
  have hgs (j : ℕ) : ∑ i, w j i * g (p j i) =
      (∑ i, w j i * (1-‖ζ j i‖)) + ‖z j-z₀‖ := by
    simp_rw [hgp, mul_add]
    rw [sum_add_distrib, ← sum_mul, hs, one_mul]
  have hconv (j : ℕ) :
      (∑ i, w j i • h j i, ∑ i, w j i*g (p j i)) ∈
        convexHull ℝ ((fun p => (f p,g p)) '' (univ : Set P)) := by
    refine mem_convexHull_of_exists_fintype (w j) (fun i => (f (p j i),g (p j i)))
      (hw j) (hs j) (fun i => ?_) ?_
    · exact ⟨p j i,mem_univ _,rfl⟩
    · apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst,
        Prod.smul_snd, f, p, smul_eq_mul]
  have hgl : Tendsto (fun j => ∑ i, w j i*g (p j i)) atTop (𝓝 0) := by
    simp only [hgs]
    have hh := hdef.add ((hz₀.sub_const z₀).norm)
    simpa only [sub_self,norm_zero,add_zero] using hh
  have hmem := mem_convexHull_zero_fiber_of_tendsto (isCompact_univ : IsCompact (univ:Set P))
    f g hf.continuousOn hg.continuousOn (fun p _ => hgn p)
    _ _ hconv he hgl
  apply (convexHull_mono ?_) hmem
  rintro a ⟨p,⟨_,hpg⟩,rfl⟩
  have hd0 := sub_nonneg.mpr (mem_closedBall_zero_iff.mp p.2.1.property)
  have hn1 := norm_nonneg (F p.2.1.val - rowComplex p.1.val p.2.2.val)
  have hn2 := le_max_left 0 (-rowPair p.1.val p.2.2.val.2)
  have hn3 := norm_nonneg (p.2.2.val-z₀)
  dsimp only [g] at hpg
  have heqz : p.2.2.val = z₀ := sub_eq_zero.mp (norm_eq_zero.mp (by linarith))
  have heqF : F p.2.1.val = rowComplex p.1.val z₀ := by
    rw [← heqz]
    exact sub_eq_zero.mp (norm_eq_zero.mp (by linarith))
  have hbd : ‖p.2.1.val‖ = 1 := by linarith
  have hpos : 0 ≤ rowPair p.1.val z₀.2 := by
    have hm : max 0 (-rowPair p.1.val p.2.2.val.2) = 0 := by linarith
    have ht := le_max_right 0 (-rowPair p.1.val p.2.2.val.2)
    rw [hm,heqz] at ht
    linarith
  have hb := (boundary_width hbd).2
  rw [heqF] at hb
  simp only [rowComplex, Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,zero_add,add_zero,sub_self,abs_of_nonneg hpos] at hb
  exact ⟨p.1.property,hb⟩

lemma rowPair_neg {n : ℕ} (a x : Fin n → ℝ) : rowPair (-a) x = -rowPair a x := by
  simp only [rowPair, Pi.neg_apply, neg_mul, sum_neg_distrib]

lemma rowComplex_neg {n : ℕ} (a : Fin n → ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    rowComplex (-a) z = -rowComplex a z := by
  simp only [rowComplex, rowPair_neg, Complex.ofReal_neg, neg_mul, neg_add_rev]
  ring

lemma planarPrimitive_nonneg_iff {m : ℕ} (hm : 0 < m) {q t : ℝ}
    (ht : t ∈ verticalFiber q) : 0 ≤ planarPrimitive m q t ↔ 0 ≤ t := by
  have hz := (verticalFiber_interval (verticalFiber_realPart ht)).2.2
  have hh := (strictMonoOn_planarPrimitive_any hm q).le_iff_le hz ht
  simpa only [planarPrimitive_zero] using hh

lemma exists_positive_strip_sample {n : ℕ} {C : Set (Fin n → ℝ)}
    (hsym : ∀ a ∈ C, -a ∈ C) {a : Fin n → ℝ} (ha : a ∈ C)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : rowComplex a z ∈ Omega)
    {m : ℕ} (hm : 0 < m) :
    ∃ b ∈ C, ∃ ζ : ℂ,
      ‖ζ‖ = ‖inverseF (rowComplex a z)‖ ∧
      F ζ = rowComplex b z ∧ 0 ≤ rowPair b z.2 ∧
      |planarPrimitive m (rowPair a z.1) (rowPair a z.2)| • b =
        (planarPrimitive m (rowPair a z.1) (rowPair a z.2)) • a := by
  have ht : rowPair a z.2 ∈ verticalFiber (rowPair a z.1) := hz
  by_cases hpos : 0 ≤ rowPair a z.2
  · refine ⟨a,ha,inverseF (rowComplex a z),rfl,inverseF_right hz,hpos,?_⟩
    rw [abs_of_nonneg ((planarPrimitive_nonneg_iff hm ht).mpr hpos)]
  · have hneg : rowPair a z.2 < 0 := lt_of_not_ge hpos
    have hp : planarPrimitive m (rowPair a z.1) (rowPair a z.2) ≤ 0 :=
      le_of_not_ge (mt (planarPrimitive_nonneg_iff hm ht).mp hpos)
    refine ⟨-a,hsym a ha,-inverseF (rowComplex a z),norm_neg _,?_,?_,?_⟩
    · rw [F_odd,inverseF_right hz,rowComplex_neg]
    · rw [rowPair_neg]; linarith
    · rw [abs_of_nonpos hp, neg_smul, smul_neg, neg_neg]

lemma strip_weights_bound {n N m : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (hm : 2 ≤ m) {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ stripSublevel A m) :
    (∑ j, |planarPrimitive m (measurement A z.1 j) (measurement A z.2 j)|) ≤
      1+(N:ℝ)*planarError m := by
  have hb (j : Fin N) := planarPrimitive_abs_bound hm (hz.1 j)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hsum : (∑ j, |planarPrimitive m (measurement A z.1 j) (measurement A z.2 j)|) ≤
      stripTau A m z + (N:ℝ)*planarError m := by
    simpa [stripCoordinate, stripTau] using hh
  have ht : stripTau A m z < 1 := hz.2
  linarith

lemma strip_concentration_bound {n N m : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (hm : 2 ≤ m) {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ stripDomain A) :
    (∑ j, |planarPrimitive m (measurement A z.1 j) (measurement A z.2 j)| *
      (1-‖inverseF (stripCoordinate A z j)‖)) ≤
      (N:ℝ) / ((2*m:ℕ)+1:ℝ) + (N:ℝ)*planarError m := by
  have hb (j : Fin N) :
      |planarPrimitive m (measurement A z.1 j) (measurement A z.2 j)| *
        (1-‖inverseF (stripCoordinate A z j)‖) ≤
        1 / ((2*m:ℕ)+1:ℝ) + planarError m := by
    have hr : ‖inverseF (stripCoordinate A z j)‖ ∈ Icc (0:ℝ) 1 :=
      ⟨norm_nonneg _,(mem_ball_zero_iff.mp (inverseF_mem (hz j))).le⟩
    have hp := planarPrimitive_abs_bound hm (hz j)
    rw [show 2*(m:ℝ)=((2*m:ℕ):ℝ) by norm_cast,Real.rpow_natCast] at hp
    have hmul := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hr.2)
    have hc := pow_mul_one_sub_le_inv hr (2*m)
    have he := mul_le_mul_of_nonneg_left (show 1-‖inverseF (stripCoordinate A z j)‖ ≤ 1 by
      linarith [hr.1]) (planarError_nonneg m)
    have hmul' : |planarPrimitive m (measurement A z.1 j) (measurement A z.2 j)| *
        (1-‖inverseF (stripCoordinate A z j)‖) ≤
        (‖inverseF (stripCoordinate A z j)‖ ^ (2*m) + planarError m) *
        (1-‖inverseF (stripCoordinate A z j)‖) := by
      simpa [stripCoordinate] using hmul
    nlinarith
  exact (sum_le_sum (fun j _ => hb j)).trans_eq (by
    rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_add,mul_one_div])

lemma exists_fast_strip_degrees (N : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, (∀ j, 2 ≤ m j) ∧
      Tendsto (fun j => (N j:ℝ)*planarError (m j)) atTop (𝓝 0) ∧
      Tendsto (fun j => (N j:ℝ)/((2*m j:ℕ)+1:ℝ)) atTop (𝓝 0) := by
  have hlim (j : ℕ) : Tendsto
      (fun m : ℕ => (N j:ℝ)*planarError m + (N j:ℝ)/((2*m:ℕ)+1:ℝ)) atTop (𝓝 0) := by
    have hf : Tendsto (fun m : ℕ => (2*m:ℕ)+1) atTop atTop := by
      apply tendsto_atTop_mono (fun m => show m ≤ 2*m+1 by omega) tendsto_id
    have hid : Tendsto (fun m : ℕ => (N j:ℝ) / ((2*m:ℕ)+1:ℝ)) atTop (𝓝 0) :=
      by
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
        (tendsto_const_nhds (x := (N j:ℝ))).div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hf)
    simpa only [mul_zero,add_zero] using
      ((planarError_nat_tendsto_zero.const_mul (N j:ℝ)).add hid)
  have hex (j : ℕ) : ∃ m : ℕ, 2 ≤ m ∧
      (N j:ℝ)*planarError m + (N j:ℝ)/((2*m:ℕ)+1:ℝ) < 1/((j:ℝ)+1) := by
    have hh := (hlim j).eventually (Iio_mem_nhds (show (0:ℝ) < 1/((j:ℝ)+1) by positivity))
    obtain ⟨m,hm,hm2⟩ := (hh.and (eventually_ge_atTop 2)).exists
    exact ⟨m,hm2,hm⟩
  choose m hm hbound using hex
  refine ⟨m,hm,?_,?_⟩
  · apply squeeze_zero (fun j => mul_nonneg (Nat.cast_nonneg _) (planarError_nonneg _))
      (fun j => le_trans (le_add_of_nonneg_right (by positivity)) (hbound j).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · apply squeeze_zero (fun j => by positivity)
      (fun j => le_trans (le_add_of_nonneg_left
        (mul_nonneg (Nat.cast_nonneg _) (planarError_nonneg _))) (hbound j).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat

lemma rowPair_sum_smul {n : ℕ} {J : Type*} [Fintype J]
    (w : J → ℝ) (h : J → Fin n → ℝ) (b : Fin n → ℝ) :
    rowPair (∑ i, w i • h i) b = ∑ i, w i * rowPair (h i) b := by
  simp only [rowPair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    sum_mul, mul_sum]
  rw [sum_comm]
  congr 1
  funext i
  apply sum_congr rfl
  intro k _
  ring

theorem common_boundary_witness_of_unnormalized {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC : IsCompact C)
    {Z : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hZ : IsCompact Z)
    (J : ℕ → Type) [∀ j, Fintype (J j)]
    (z : ℕ → ((Fin n → ℝ) × (Fin n → ℝ))) (hz : ∀ j, z j ∈ Z)
    (h : ∀ j, J j → Fin n → ℝ) (w : ∀ j, J j → ℝ) (ζ : ∀ j, J j → ℂ)
    (hh : ∀ j i, h j i ∈ C) (hw : ∀ j i, 0 ≤ w j i)
    (hd : ∀ j i, ‖ζ j i‖ ≤ 1)
    (hF : ∀ j i, F (ζ j i) = rowComplex (h j i) (z j))
    (hy : ∀ j i, 0 ≤ rowPair (h j i) (z j).2)
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hz₀ : Tendsto z atTop (𝓝 z₀))
    {e : Fin n → ℝ} (he : Tendsto (fun j => ∑ i, w j i • h j i) atTop (𝓝 e))
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hs : ∀ j, ∑ i, w j i ≤ 1+err j)
    (hdef : Tendsto (fun j => ∑ i, w j i * (1-‖ζ j i‖)) atTop (𝓝 0))
    (b : Fin n → ℝ) (hb : ∀ a ∈ C, rowPair a b ≤ 1) (heb : rowPair e b = 1) :
    e ∈ convexHull ℝ {a ∈ C | rowPair a z₀.2 = lensWidth (rowPair a z₀.1)} := by
  classical
  let σ (j : ℕ) : ℝ := ∑ i, w j i
  have hσ : Tendsto σ atTop (𝓝 1) := by
    have hlo (j : ℕ) : rowPair (∑ i, w j i • h j i) b ≤ σ j := by
      rw [rowPair_sum_smul]
      apply sum_le_sum
      intro i _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb _ (hh j i)) (hw j i)
    have hlow : Tendsto (fun j => rowPair (∑ i, w j i • h j i) b) atTop (𝓝 1) := by
      rw [← heb]
      exact (continuous_rowPair.tendsto (e,b)).comp (he.prodMk_nhds tendsto_const_nhds)
    have hupp : Tendsto (fun j => 1+err j) atTop (𝓝 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add herr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp hlo hs
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hσ.eventually (Ioi_mem_nhds zero_lt_one))
  let t (k : ℕ) := k+N
  have ht : Tendsto t atTop atTop := tendsto_add_atTop_nat N
  have hpos (k : ℕ) : 0 < σ (t k) := hN _ (Nat.le_add_left _ _)
  let wn (k : ℕ) (i : J (t k)) := (σ (t k))⁻¹ * w (t k) i
  have hnorm (k : ℕ) : ∑ i, wn k i = 1 := by
    rw [show (∑ i, wn k i) = (σ (t k))⁻¹ * σ (t k) by simp only [wn,σ,mul_sum]]
    exact inv_mul_cancel₀ (hpos k).ne'
  have hinv : Tendsto (fun k => (σ (t k))⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one,Function.comp_def] using (hσ.comp ht).inv₀ (one_ne_zero : (1:ℝ) ≠ 0)
  apply common_boundary_witness_of_concentration hC hZ (fun k => J (t k))
    (fun k => z (t k)) (fun k => hz (t k)) (fun k => h (t k)) wn
    (fun k => ζ (t k)) (fun k => hh (t k))
    (fun k i => mul_nonneg (inv_nonneg.mpr (hpos k).le) (hw _ _)) hnorm
    (fun k => hd (t k)) (fun k => hF (t k)) (fun k => hy (t k)) (hz₀.comp ht)
  · have he' := hinv.smul (he.comp ht)
    simpa only [Function.comp_def,one_smul, wn, mul_smul, smul_sum,smul_eq_mul] using he'
  · have he' := hinv.mul (hdef.comp ht)
    simpa only [Function.comp_def,mul_zero, wn, mul_assoc, mul_sum] using he'

open Set Filter Finset Metric Complex MeasureTheory
open scoped Topology
open MahlerConformal

lemma rowComplex_eq_stripCoordinate {n N : ℕ}
    (A : Matrix (Fin N) (Fin n) ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin N) :
    rowComplex (A i) z = stripCoordinate A z i := rfl

lemma push_eq_sum_smul {I J : Type*} [Fintype I] [Fintype J]
    (A : J → I → ℝ) (p : J → ℝ) : push A p = ∑ i, p i • A i := by
  ext k
  simp only [push,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]

lemma strip_prefix_compact {n : ℕ} (C : Set (Fin n → ℝ)) (a : ℕ → C)
    (ha : Function.Injective (measurement (fun i : Fin n => (a i).val))) :
    ∃ Z : Set ((Fin n → ℝ) × (Fin n → ℝ)), IsCompact Z ∧
      ∀ N : ℕ, stripDomain (fun i : Fin (n+N) => (a i).val) ⊆ Z := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i => (a i).val
  refine ⟨stripCoordinate A ⁻¹' {f | ∀ i, f i ∈ closure Omega},
    stripCoordinate_compact_preimage A ha (isCompact_pi_infinite (fun _ => isCompact_closure_Omega)),?_⟩
  intro N z hz i
  exact subset_closure (hz ⟨i.val,by omega⟩)

lemma closed_lens_constraints_of_dense_prefix_limit {n : ℕ}
    (C : Set (Fin n → ℝ)) (a : ℕ → C) (hdense : DenseRange a)
    (j : ℕ → ℕ) (hj : Tendsto j atTop atTop)
    (z : ℕ → ((Fin n → ℝ) × (Fin n → ℝ)))
    (hz : ∀ k, z k ∈ stripDomain (fun i : Fin (n+j k) => (a i).val))
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hlim : Tendsto z atTop (𝓝 z₀)) :
    ∀ h ∈ C, rowComplex h z₀ ∈ closure Omega := by
  intro h hh
  have hs : IsClosed {h : C | rowComplex h.val z₀ ∈ closure Omega} :=
    isClosed_closure.preimage
      (continuous_rowComplex.comp (continuous_subtype_val.prodMk continuous_const))
  refine hdense.induction_on (p := fun h : C => rowComplex h.val z₀ ∈ closure Omega)
    (⟨h,hh⟩ : C) hs ?_
  intro i
  apply isClosed_closure.mem_of_tendsto
    ((continuous_rowComplex.tendsto ((a i).val,z₀)).comp
      (tendsto_const_nhds.prodMk_nhds hlim))
  filter_upwards [hj.eventually (eventually_ge_atTop (i+1))] with k hk
  exact subset_closure (hz k ⟨i,by omega⟩)

theorem equality_common_lens_witness {n : ℕ} (hn : 1 ≤ n)
    {B : Set (Fin n → ℝ)} (hB : IsCompact B) (hconv : Convex ℝ B)
    (hsym : ∀ x ∈ B, -x ∈ B) (hint : (interior B).Nonempty)
    (heq : (volume B).toReal * (volume (coordinatePolar B)).toReal =
      (4:ℝ)^n/(Nat.factorial n:ℝ))
    {x e b : Fin n → ℝ} (hx : x ∈ B) (he : e ∈ coordinatePolar B)
    (hb : b ∈ B) (heb : rowPair e b = 1) :
    ∃ y : Fin n → ℝ,
      (∀ a ∈ coordinatePolar B, |rowPair a y| ≤ lensWidth (rowPair a x)) ∧
      e ∈ convexHull ℝ {a ∈ coordinatePolar B | rowPair a y = lensWidth (rowPair a x)} := by
  classical
  let C := coordinatePolar B
  obtain ⟨hC,hCc,hCs,hCi⟩ := coordinatePolar_is_symmetric_convex_body hB hconv hsym hint
  obtain ⟨a,hadense,_,hainj,hacomp,_,hasub,_,havol,_⟩ :=
    exists_finite_strip_approximation hn hB hconv hsym hint
  obtain ⟨m,hm,herr,hinterior⟩ := exists_fast_strip_degrees (fun j => n+j)
  obtain ⟨j,z,hj,hz,hmaplim⟩ := equality_strip_images_dense hn hB hconv hsym hint heq
    a hainj (fun j => (hacomp j).1) hasub havol m hm herr hx he
  have ha0 : Function.Injective (measurement (fun i : Fin n => (a i).val)) := by
    simpa only [Nat.add_zero] using hainj 0
  obtain ⟨Z,hZ,hcontain⟩ := strip_prefix_compact C a ha0
  obtain ⟨z₀,hz₀Z,φ,hφ,hφlim⟩ := hZ.tendsto_subseq (fun k => hcontain (j k) (hz k).1)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  let t (k : ℕ) := j (φ k)
  let v (k : ℕ) := z (φ k)
  let A (k : ℕ) : Matrix (Fin (n+t k)) (Fin n) ℝ := fun i => (a i).val
  let J (k : ℕ) := Fin (n+t k)
  have hv (k : ℕ) : v k ∈ stripSublevel (A k) (m (t k)) := hz (φ k)
  have hvlim : Tendsto v atTop (𝓝 z₀) := hφlim
  have ht : Tendsto t atTop atTop := hj.comp hφtop
  have hmap : Tendsto (fun k => stripMap (A k) (m (t k)) (v k)) atTop (𝓝 (x,e)) :=
    hmaplim.comp hφtop
  have hvfst : Tendsto (fun k => (v k).1) atTop (𝓝 x) := by
    simpa only [Function.comp_def,stripMap] using (continuous_fst.tendsto (x,e)).comp hmap
  have hzx : z₀.1 = x := tendsto_nhds_unique ((continuous_fst.tendsto z₀).comp hvlim) hvfst
  have hsamples (k : ℕ) (i : J k) :
      ∃ b ∈ C, ∃ ζ : ℂ,
        ‖ζ‖ = ‖inverseF (rowComplex (A k i) (v k))‖ ∧
        F ζ = rowComplex b (v k) ∧ 0 ≤ rowPair b (v k).2 ∧
        |planarPrimitive (m (t k)) (rowPair (A k i) (v k).1) (rowPair (A k i) (v k).2)| • b =
          planarPrimitive (m (t k)) (rowPair (A k i) (v k).1) (rowPair (A k i) (v k).2) • A k i :=
    exists_positive_strip_sample hCs (a i).property ((hv k).1 i) (by have := hm (t k); omega)
  choose h hh ζ hnorm hF hy hsigned using hsamples
  let w (k : ℕ) (i : J k) : ℝ :=
    |planarPrimitive (m (t k)) (rowPair (A k i) (v k).1) (rowPair (A k i) (v k).2)|
  have hsum (k : ℕ) : (∑ i, w k i • h k i) = (stripMap (A k) (m (t k)) (v k)).2 := by
    simp only [w,hsigned,stripMap]
    rw [push_eq_sum_smul]
    rfl
  have hwlim : Tendsto (fun k => ∑ i, w k i • h k i) atTop (𝓝 e) := by
    simpa only [hsum,Function.comp_def] using ((continuous_snd.tendsto (x,e)).comp hmap)
  have hwupper (k : ℕ) : ∑ i, w k i ≤ 1+((n+t k:ℕ):ℝ)*planarError (m (t k)) :=
    strip_weights_bound (A k) (hm (t k)) (hv k)
  have hdef : Tendsto (fun k => ∑ i, w k i * (1-‖ζ k i‖)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun k => sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr ?_)))
      (fun k => ?_)
      (show Tendsto (fun k => ((n+t k:ℕ):ℝ)/((2*m (t k):ℕ)+1:ℝ) +
          ((n+t k:ℕ):ℝ)*planarError (m (t k))) atTop (𝓝 0) from
        by simpa only [add_zero,Function.comp_def] using (hinterior.comp ht).add (herr.comp ht))
    · rw [hnorm]
      exact (mem_ball_zero_iff.mp (inverseF_mem ((hv _).1 _))).le
    · simpa only [hnorm,w,rowComplex_eq_stripCoordinate,rowPair,measurement] using
        strip_concentration_bound (A k) (hm (t k)) (hv k).1
  have hboundary := common_boundary_witness_of_unnormalized hC hZ J v
    (fun k => hcontain _ (hv k).1) h w ζ hh (fun _ _ => abs_nonneg _) (fun k i =>
      (hnorm k i).trans_le (mem_ball_zero_iff.mp (inverseF_mem ((hv k).1 i))).le)
    hF hy hvlim hwlim _ (herr.comp ht) hwupper hdef b
    (fun a ha => ha b hb) heb
  have hall := closed_lens_constraints_of_dense_prefix_limit C a hadense t ht v
    (fun k => (hv k).1) hvlim
  refine ⟨z₀.2,?_,?_⟩
  · intro a ha
    have hh := closure_Omega_width_bound (hall a ha)
    simpa [rowComplex,hzx] using hh
  · simpa only [hzx] using hboundary

open Set Finset MeasureTheory
open MahlerConformal
namespace RealNormData

def segmentEquiv {n : ℕ} (h : RealNormData (Fin n → ℝ)) :
    (h.Space × ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) :=
  (h.spaceEquiv.prodCongr (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm).trans (appendEquiv n 1)

@[simp] lemma segmentEquiv_apply {n : ℕ} (h : RealNormData (Fin n → ℝ)) (p : h.Space) (a : ℝ) :
    h.segmentEquiv (p,a) = Fin.append (h.spaceEquiv p) (fun _ => a) := rfl

lemma lifted_pair {n : ℕ} (h : RealNormData (Fin n → ℝ)) (p : h.Space) (a : ℝ)
    (v : Fin n → ℝ) (t : ℝ) :
    rowPair (h.segmentEquiv (p,a)) (Fin.append v (fun _ : Fin 1 => t)) =
      (∑ i, (h.spaceEquiv p) i*v i)+a*t := by
  simp only [rowPair,segmentEquiv_apply,dot_append,Fin.sum_univ_one]

theorem optimal_lift_of_equality {n : ℕ} (hn : 0 < n)
    {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h)
    (heq : (volume g.unit).toReal * (volume h.unit).toReal = (4:ℝ)^n/Nat.factorial n) :
    HasOptimalLiftRepresentations lensWidth h.Space := by
  intro u hu δ hδ hδ1 q a hq
  obtain ⟨v,hv,huv⟩ := coordinate_of_dual hd u
  let c := interval 1 (by norm_num : (0:ℝ) < 1)
  let G := g.coordSum c
  let H := h.coordMax c
  obtain ⟨hdual,heqlift⟩ := equality_segment_lift hn hd heq
  change G.IsDual H at hdual
  change (volume G.unit).toReal * (volume H.unit).toReal = _ at heqlift
  let T : ℝ := Max.max ‖q‖ |a|
  have hT : 0 < T := (norm_pos_iff.mpr hq).trans_le (le_max_left _ _)
  let e := T⁻¹ • h.segmentEquiv (q,a)
  let x : Fin (n+1) → ℝ := Fin.append (δ • v) (fun _ => 1-δ)
  have hx : x ∈ G.unit := by
    change g.coordSum c (Fin.append (δ • v) (fun _ => 1-δ)) ≤ 1
    rw [coordSum_append,g.smul_eq,abs_of_pos hδ,interval_apply,div_one,
      abs_of_nonneg (sub_nonneg.mpr hδ1.le)]
    have hh := mul_le_mul_of_nonneg_left (hv.trans hu.le) hδ.le
    linarith
  have hHe : H e = 1 := by
    change H (T⁻¹ • h.segmentEquiv (q,a)) = 1
    rw [H.smul_eq, abs_of_pos (inv_pos.mpr hT)]
    have hh : H (h.segmentEquiv (q,a)) = T := by
      simp only [H,segmentEquiv_apply,coordMax_append,c,interval_apply,div_one,T,space_norm]
    rw [hh,inv_mul_cancel₀ hT.ne']
  obtain ⟨b,hb,heb⟩ := hdual.2 e
  have he : e ∈ coordinatePolar G.unit := by
    rw [hdual.polar_unit]
    exact hHe.le
  obtain ⟨y,hy,hcontact⟩ := equality_common_lens_witness (show 1 ≤ n+1 by omega)
    G.isCompact_unit G.convex_unit G.symmetric_unit G.interior_unit_nonempty
    (by rw [hdual.polar_unit]; exact heqlift) hx he hb (heb.trans hHe)
  let doty : (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun z => rowPair z y
    map_add' := by intro z w; simp [rowPair,add_mul,sum_add_distrib]
    map_smul' := by intro r z; simp [rowPair,mul_assoc,← mul_sum] }
  let L := doty.comp h.segmentEquiv.toLinearMap
  have hL (z : h.Space × ℝ) : L z = rowPair (h.segmentEquiv z) y := rfl
  have hnorm (z : h.Space × ℝ) : h.segmentEquiv z ∈ coordinatePolar G.unit ↔
      ‖z.1‖ ≤ 1 ∧ |z.2| ≤ 1 := by
    rcases z with ⟨p,s⟩
    rw [hdual.polar_unit]
    simp only [unit,segmentEquiv_apply,H,coordMax_append,c,interval_apply,div_one,space_norm,Set.mem_ofPred_eq,max_le_iff]
  have hpair (z : h.Space × ℝ) : rowPair (h.segmentEquiv z) x = δ*u z.1+(1-δ)*z.2 := by
    rw [lifted_pair,huv]
    simp only [Pi.smul_apply,smul_eq_mul]
    simp_rw [show ∀ i, (h.spaceEquiv z.1) i*(δ*v i) = δ*((h.spaceEquiv z.1) i*v i) by intro i; ring]
    rw [← mul_sum]
    ring
  apply optimal_signed_of_common_lens lensWidth_even concaveOn_lensWidth u hu.le hδ.le hδ1.le hT L
  · intro p hp s hs
    rw [hL,← hpair (p,s)]
    exact (le_abs_self _).trans (hy _ ((hnorm (p,s)).mpr ⟨hp,hs⟩))
  · have hmem : h.segmentEquiv.symm e ∈ convexHull ℝ
        (h.segmentEquiv.symm '' {z ∈ coordinatePolar G.unit | rowPair z y = lensWidth (rowPair z x)}) := by
      change _ ∈ convexHull ℝ (h.segmentEquiv.symm.toLinearMap '' _)
      rw [← h.segmentEquiv.symm.toLinearMap.image_convexHull]
      exact mem_image_of_mem _ hcontact
    have hem : h.segmentEquiv.symm e = (T⁻¹ • q,T⁻¹*a) := by
      simp only [e,map_smul,LinearEquiv.symm_apply_apply,Prod.smul_mk,smul_eq_mul]
    rw [hem] at hmem
    apply (convexHull_mono ?_) hmem
    rintro _ ⟨z,⟨hz,hze⟩,rfl⟩
    have hm := (hnorm (h.segmentEquiv.symm z)).mp (by simpa using hz)
    refine ⟨hm.1,hm.2,?_⟩
    rw [hL,LinearEquiv.apply_symm_apply,hze,← hpair,LinearEquiv.apply_symm_apply]

theorem medians_of_equality {n : ℕ} (hn : 0 < n)
    {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h)
    (heq : (volume g.unit).toReal * (volume h.unit).toReal = (4:ℝ)^n/Nat.factorial n) :
    HasMetricMedians h.Space :=
  metricMedians_of_optimal_lift lensWidth_endpoint_scaling (optimal_lift_of_equality hn hd heq)

end RealNormData

open Set MeasureTheory Metric

theorem equality_polar_gauge_medians {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hs : ∀ x ∈ K, -x ∈ K) (hi : (interior K).Nonempty)
    (heq : (volume K).toReal * (volume (coordinatePolar K)).toReal = (4:ℝ)^n/Nat.factorial n) :
    ∃ g h : RealNormData (Fin n → ℝ), g.unit = K ∧ h.unit = coordinatePolar K ∧
      g.IsDual h ∧ HasMetricMedians h.Space ∧ HasMetricMedians g.Space := by
  obtain ⟨hP,hPc,hPs,hPi⟩ := coordinatePolar_is_symmetric_convex_body hK hc hs hi
  let g := bodyNorm hK hc hs hi
  let h := bodyNorm hP hPc hPs hPi
  have hg : g.unit = K := bodyNorm_unit hK hc hs hi
  have hh : h.unit = coordinatePolar K := bodyNorm_unit hP hPc hPs hPi
  have hd := g.isDual_of_polar h (by rw [hg,hh])
  have hv : (volume g.unit).toReal * (volume h.unit).toReal = (4:ℝ)^n/Nat.factorial n := by
    rwa [hg,hh]
  refine ⟨g,h,hg,hh,hd,RealNormData.medians_of_equality hn hd hv,?_⟩
  exact RealNormData.medians_of_equality hn hd.symm (by simpa only [mul_comm] using hv)

end SymmetricMahler

end

end OAI
