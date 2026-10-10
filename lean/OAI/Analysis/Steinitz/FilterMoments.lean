import OAI.Analysis.Steinitz.GaussianTail

namespace OAI

/-! Filtered moments, prefix bounds, and rank-one contractions. -/

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma cutoff_size {x : ℝ} (hx : 0 ≤ x) (hf : cutoff x≠0) : 1/4 ≤ sizeWeight x := by
  have hb : 1/2 ≤ x ∧ x ≤ 4 := by
    by_contra h
    exact hf (cutoff_zero_of_not_band h)
  have hp : 0<x := by linarith
  unfold sizeWeight
  rw [show exponent-1=(1/2:ℝ) by norm_num [exponent],← Real.sqrt_eq_rpow]
  apply le_min
  · exact (Real.le_sqrt (by norm_num) hx).mpr (by nlinarith)
  · exact (le_inv_comm₀ (by norm_num) hp).mpr (by norm_num; linarith)

lemma cutoff_square_size {x : ℝ} (hx : 0 ≤ x) : cutoff x^2 ≤ 4*sizeWeight x := by
  by_cases hf : cutoff x=0
  · rw [hf,zero_pow (by decide : 2≠0)]; positivity [Scale.size_nonneg hx]
  · have hs := cutoff_size hx hf
    have ha := cutoff_nonneg x
    have hb := cutoff_le_one x
    nlinarith

lemma cutoff_scaled_size {x : ℝ} (hx : 0 ≤ x) : x*cutoff x^2 ≤ 16*sizeWeight x := by
  by_cases hf : cutoff x=0
  · rw [hf,zero_pow (by decide : 2≠0),mul_zero]; positivity [Scale.size_nonneg hx]
  · have hb : x ≤ 4 := by
      by_contra h
      exact hf (cutoff_zero_of_not_band (by tauto))
    have hs := cutoff_size hx hf
    have ha := cutoff_nonneg x
    have hc := cutoff_le_one x
    have ht : cutoff x^2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht hx]

omit [DecidableEq κ] in
lemma squareMass_weighted (B : Matrix κ ι ℝ) : squareMass B=weightedSq B 1 := by
  rw [weightedSq,Matrix.mul_one,Matrix.trace_mul_comm,gram_trace]

omit [DecidableEq κ] in
lemma squareMass_le_weighted (B : Matrix κ ι ℝ) {q : ι → ℝ} (hq : ∀ i,0 ≤ q i) :
    squareMass B ≤ weightedSq B (1+diagonal q) := by
  rw [weightedSq_weight_add,← squareMass_weighted]
  exact le_add_of_nonneg_right (weightedSq_nonneg B (PosSemidef.diagonal hq))

lemma coisometry_norm_le {R : Matrix ι κ ℝ} (hR : R*R.transpose=1) : ‖R‖ ≤ 1 := by
  have he := Matrix.l2_opNorm_conjTranspose_mul_self R.transpose
  simp only [conjTranspose_eq_transpose_of_trivial,transpose_transpose,hR] at he
  have ht : ‖R.transpose‖=‖R‖ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose R
  have ho : ‖(1 : Matrix ι ι ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one,Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun _ => by norm_num)
  rw [ht] at he
  nlinarith [norm_nonneg R]

lemma cutoff_norm_le (X : Matrix ι ι ℝ) : ‖cfc cutoff X‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num)
  intro x _
  rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_nonneg x)]
  exact cutoff_le_one x

lemma lift_cutoff_contract {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {X : Matrix ι ι ℝ} (_hX : X.IsHermitian) (x : EuclideanSpace ℝ κ) :
    ‖matrixMap (lift R (cfc cutoff X)) x‖^2 ≤ ‖x‖^2 := by
  have hr := coisometry_norm_le hR
  have ht : ‖R.transpose‖ ≤ 1 := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose R).le.trans hr
  have hn : ‖lift R (cfc cutoff X)‖ ≤ 1 := by
    exact (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul
      ((Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul ht (cutoff_norm_le X)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))) hr
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have hv : ‖matrixMap (lift R (cfc cutoff X)) x‖ ≤ ‖x‖ := by
    exact (Matrix.l2_opNorm_mulVec _ x).trans
      ((mul_le_mul_of_nonneg_right hn (norm_nonneg x)).trans_eq (one_mul _))
  exact pow_le_pow_left₀ (norm_nonneg _) hv 2

lemma lift_cutoff_mass {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) :
    squareMass (lift R (cfc cutoff X)) ≤ 4*(cfc sizeWeight X).trace := by
  rw [squareMass_weighted,weighted_lift R hR,Matrix.mul_one,hR,
    weightedSq_cfc hX.1,Matrix.mul_one,trace_cfc hX.1,trace_cfc hX.1,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => cutoff_square_size (hX.eigenvalues_nonneg i)

omit [Fintype κ] [DecidableEq κ] in
lemma lift_cutoff_size {R : Matrix ι κ ℝ} {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (hf : lift R (cfc cutoff X)≠0) : 1/4 ≤ (cfc sizeWeight X).trace := by
  have he : ∃ i,cutoff (hX.1.eigenvalues i)≠0 := by
    by_contra! h
    apply hf
    rw [real_cfc hX.1]
    simp [h,lift]
  obtain ⟨i,hi⟩ := he
  rw [trace_cfc hX.1]
  exact (cutoff_size (hX.eigenvalues_nonneg i) hi).trans
    (Finset.single_le_sum (fun j _ => Scale.size_nonneg (hX.eigenvalues_nonneg j)) (Finset.mem_univ i))

omit [DecidableEq κ] in
lemma weightedSq_diagonal_mono (B : Matrix κ ι ℝ) {q r : ι → ℝ}
    (hqr : ∀ i,q i ≤ r i) : weightedSq B (diagonal q) ≤ weightedSq B (diagonal r) := by
  have hp : (diagonal (fun i => r i-q i)).PosSemidef :=
    PosSemidef.diagonal (fun i => sub_nonneg.mpr (hqr i))
  have hh := weightedSq_nonneg B hp
  have he : diagonal r=diagonal q+diagonal (fun i => r i-q i) := by
    rw [diagonal_add]; congr 1; funext i; simp
  rw [he,weightedSq_weight_add]
  linarith

lemma lift_cutoff_time {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {q : κ → ℝ} (hq : ∀ j,0<q j) {θ : ℝ} (hθ : 0<θ) :
    weightedSq (lift R (cfc cutoff (state (fun j => q j/θ) R))) (diagonal q) ≤
      16*(cfc sizeWeight (state (fun j => q j/θ) R)).trace*θ := by
  let X := state (fun j => q j/θ) R
  have hX : X.PosDef := state_posDef hR (fun j => div_pos (hq j) hθ)
  have he : R*diagonal q*R.transpose=θ • X := by
    dsimp [X,state]
    have hd : θ • diagonal (fun j => q j/θ)=diagonal q := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext j
      change θ*(q j/θ)=q j
      field_simp
    rw [← Matrix.smul_mul,← Matrix.mul_smul,hd]
  have hec : cfc (fun x => cutoff x^2) X*X=cfc (fun x => cutoff x^2*x) X := by
    conv_lhs => arg 2; rw [← cfc_id' ℝ X hX.1.isSelfAdjoint]
    exact cfc_mul_same hX.1 _ _
  rw [weighted_lift R hR,he,weightedSq_cfc hX.1,Matrix.mul_smul,Matrix.trace_smul,hec,
    trace_cfc hX.1,trace_cfc hX.1]
  change θ*(∑ i,cutoff (hX.1.eigenvalues i)^2*hX.1.eigenvalues i) ≤ _
  have hh := Finset.sum_le_sum (fun (i : ι) (_ : i∈Finset.univ) =>
    cutoff_scaled_size (hX.eigenvalues_pos i).le)
  rw [← Finset.mul_sum] at hh
  have hh' : (∑ i,cutoff (hX.1.eigenvalues i)^2*hX.1.eigenvalues i) ≤
      16*∑ i,sizeWeight (hX.1.eigenvalues i) := by simpa only [mul_comm] using hh
  nlinarith

end EuclideanSteinitz.Filter

end

section

namespace EuclideanSteinitz.Energy
open Matrix Gain
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma finish_append (A : Matrix ι ι ℝ) (ps qs : List (Move ι)) :
    finish A (ps++qs)=finish (finish A ps) qs := by
  induction ps generalizing A with
  | nil => rfl
  | cons p ps ih => exact ih (p.next A)

lemma cost_append (A : Matrix ι ι ℝ) (ps qs : List (Move ι)) :
    cost A (ps++qs)=cost A ps+cost (finish A ps) qs := by
  induction ps generalizing A with
  | nil => simp [cost,finish]
  | cons p ps ih => simp only [List.cons_append,cost,finish,ih,add_assoc]

lemma cost_prefix {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {ps qs : List (Move ι)}
    (hp : ∀ p∈qs,p.Admissible) (h : ps <+: qs) : cost A ps ≤ cost A qs := by
  obtain ⟨rs,rfl⟩ := h
  rw [cost_append]
  exact le_add_of_nonneg_right (cost_nonneg
    (EuclideanSteinitz.ScaleEnergy.finish_psd hA (fun p h => hp p (List.mem_append_left _ h)))
    (fun p h => hp p (List.mem_append_right _ h)))

end EuclideanSteinitz.Energy

namespace EuclideanSteinitz.Filter
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq ι] in
lemma run_append (R : Matrix ι κ ℝ) (ps qs : List (Step ι κ)) :
    run R (ps++qs)=run (run R ps) qs := by
  induction ps generalizing R with
  | nil => rfl
  | cons p ps ih => exact ih (p.apply R)

omit [Fintype κ] [DecidableEq ι] in
lemma run_fresh_append {R : Matrix ι κ ℝ} {ps qs : List (Step ι κ)}
    (hf : Fresh R (ps++qs)) (hd : ((ps++qs).map Step.j).Nodup) : Fresh (run R ps) qs := by
  induction ps generalizing R with
  | nil => exact hf
  | cons p ps ih =>
    have hh := List.nodup_cons.mp hd
    apply ih (R := p.apply R) _ hh.2
    apply Step.fresh_tail hf
    intro q hq he
    exact hh.1 (List.mem_map.mpr ⟨q,hq,he.symm⟩)

omit [Fintype κ] [DecidableEq κ] in
lemma good_prefix {ps qs : List (Step ι κ)} (hp : ∀ p∈qs,p.Good) (h : ps <+: qs) :
    ∀ p∈ps,p.Good := fun p hp' => hp p (h.subset hp')

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma fresh_prefix {R : Matrix ι κ ℝ} {ps qs : List (Step ι κ)} (hf : Fresh R qs) (h : ps <+: qs) :
    Fresh R ps := fun p hp => hf p (h.subset hp)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma nodup_prefix {ps qs : List (Step ι κ)} (hd : (qs.map Step.j).Nodup) (h : ps <+: qs) :
    (ps.map Step.j).Nodup := (h.map _).sublist.nodup hd

omit [Fintype κ] [DecidableEq κ] in
lemma moves_good {ps : List (Step ι κ)} (hp : ∀ p∈ps,p.Good) {q : κ → ℝ} (hq : ∀ j,0≤q j) :
    ∀ p∈ps.map (fun p => p.move q),p.Admissible := by
  intro p hp'
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp'
  exact Step.admissible (hp r hr) hq

lemma cost_prefix_difference {R : Matrix ι κ ℝ} {ps qs : List (Step ι κ)}
    (hf : Fresh R (ps++qs)) (hd : ((ps++qs).map Step.j).Nodup) (q : κ → ℝ) :
    cost (state q R) ((ps++qs).map (fun p => p.move q)) -
      cost (state q R) (ps.map (fun p => p.move q)) =
      cost (state q (run R ps)) (qs.map (fun p => p.move q)) := by
  rw [List.map_append,cost_append,← run_state q (fresh_prefix hf (List.prefix_append _ _))
    (nodup_prefix hd (List.prefix_append _ _))]
  ring

lemma local_prefix_increment {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    {ps qs : List (Step ι κ)} (hps : ps <+: qs) (hqs : qs <+: L)
    {q : κ → ℝ} (hq : ∀ j,0<q j)
    (hsmall : cost (state q R) (qs.map (fun p => p.move q)) -
      cost (state q R) (ps.map (fun p => p.move q)) ≤ 1/(16*gainConstant)) :
    Coefficient.weightedSq
      (Coefficient.lift (run R qs) (cfc cutoff (state q (run R qs))) -
       Coefficient.lift (run R ps) (cfc cutoff (state q (run R ps)))) (1+diagonal q) ≤
      incrementConstant*(1+(cfc sizeWeight (state q (run R qs))).trace)*
      (cost (state q R) (qs.map (fun p => p.move q)) -
       cost (state q R) (ps.map (fun p => p.move q)))^(1/exponent) := by
  obtain ⟨rs,rfl⟩ := hps
  have hp' := good_prefix hp hqs
  have hf' := fresh_prefix hf hqs
  have hd' := nodup_prefix hd hqs
  have hc := cost_prefix_difference hf' hd' q
  rw [hc] at hsmall ⊢
  rw [run_append]
  exact weighted_increment
    (run_coisometry hR (good_prefix hp' (List.prefix_append _ _))
      (fresh_prefix hf' (List.prefix_append _ _)) (nodup_prefix hd' (List.prefix_append _ _)))
    (fun p h => hp' p (List.mem_append_right _ h)) (run_fresh_append hf' hd')
    (by rw [List.map_append] at hd'; exact (List.nodup_append.mp hd').2.1)
    hq le_rfl hsmall

end EuclideanSteinitz.Filter

end

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient ScaleEnergy Energy
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma coisometry_column {R : Matrix ι κ ℝ} (hR : R*R.transpose=1) (j : κ) :
    (∑ i,R i j^2) ≤ 1 := by
  have h := Matrix.l2_opNorm_mulVec R (EuclideanSpace.single j (1:ℝ))
  have hn : ‖(EuclideanSpace.single j (1:ℝ))‖=1 := by simp
  rw [hn,mul_one] at h
  have hh : ‖matrixMap R (EuclideanSpace.single j 1)‖≤1 := h.trans (coisometry_norm_le hR)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  rw [EuclideanSpace.real_norm_sq_eq] at hs
  simpa [matrixMap,Matrix.toEuclideanLin,Matrix.mulVec,PiLp.single_apply] using hs

lemma state_trace_le {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {q : κ → ℝ} (hq : ∀ j,0≤q j) : (state q R).trace ≤ ∑ j,q j := by
  calc
    _ = ∑ j,q j*(∑ i,R i j^2) := by
      change (∑ i,∑ j,(R*diagonal q) i j*R.transpose j i)=_
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ j,q j := Finset.sum_le_sum fun j _ => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (coisometry_column hR j) (hq j)

omit [Fintype κ] [DecidableEq κ] in
lemma Step.b_square_le {p : Step ι κ} (hp : p.Good) : ∑ i,p.b i^2 ≤ 1 := by
  have hc : (p.C*p.C.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose p.C
  have he : p.C*p.C.transpose = 1-vecMulVec p.b p.b := by rw [← hp.2]; abel
  rw [he] at hc
  have hh := hc.dotProduct_mulVec_nonneg p.b
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub,
    Matrix.vecMulVec_mulVec,dotProduct_smul,op_smul_eq_mul] at hh
  have hbb : p.b ⬝ᵥ p.b=∑ i,p.b i^2 := by simp only [dotProduct,pow_two]
  rw [hbb] at hh
  nlinarith [Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => sq_nonneg (p.b i))]

lemma gains_le_total {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hd : (L.map Step.j).Nodup)
    {q : κ → ℝ} (hq : ∀ j,0≤q j) : gainSum (L.map (fun p => p.move q)) ≤ ∑ j,q j := by
  have hterm (p : Step ι κ) (h : p∈L) : (p.move q).gain.trace ≤ q p.j := by
    change (q p.j • vecMulVec p.b p.b).trace ≤ _
    rw [Matrix.trace_smul]
    have ht : (vecMulVec p.b p.b).trace=∑ i,p.b i^2 := by simp [Matrix.trace,vecMulVec_apply,pow_two]
    rw [ht,smul_eq_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Step.b_square_le (hp p h)) (hq p.j)
  calc
    gainSum (L.map (fun p => p.move q)) = (L.map (fun p => (p.move q).gain.trace)).sum := by simp only [gainSum,List.map_map,Function.comp_def]
    _ ≤ (L.map (fun p => q p.j)).sum := List.sum_le_sum hterm
    _ = ∑ j∈(L.map Step.j).toFinset,q j := by
      rw [List.sum_toFinset _ hd]
      simp only [List.map_map,Function.comp_def]
    _ ≤ ∑ j,q j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hq j)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma move_scale (p : Step ι κ) (q : κ → ℝ) (θ : ℝ) :
    p.move (fun j => q j/θ) = rescale θ⁻¹ (p.move q) := by
  cases p
  simp only [Step.move,rescale]
  congr 1
  rw [smul_smul]
  congr 1
  simp [div_eq_mul_inv,mul_comm]

lemma sum_epoch_cost {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hd : (L.map Step.j).Nodup)
    {q : κ → ℝ} (hq : ∀ j,0≤q j) (S : Finset ℤ) :
    (∑ k∈S,(2:ℝ)^k*cost (((2:ℝ)^k)⁻¹ • state q R)
      (L.map (fun p => p.move (fun j => q j/(2:ℝ)^k)))) ≤ 84*(∑ j,q j) := by
  simp only [move_scale,show ∀ c, L.map (fun p => rescale c (p.move q)) =
    (L.map (fun p => p.move q)).map (rescale c) from fun c => by simp only [List.map_map,Function.comp_def]]
  have hstate : (state q R).PosSemidef := by
    change (R*diagonal q*R.transpose).PosSemidef
    simpa only [conjTranspose_eq_transpose_of_trivial] using (PosSemidef.diagonal hq).mul_mul_conjTranspose_same R
  exact (scale_energy_bound hstate (moves_good hp hq) S).trans (by
    have h₁ := state_trace_le hR hq
    have h₂ := gains_le_total hp hd hq
    linarith)

lemma sum_dyadic_le {S : Finset ℤ} {b : ℝ} (hb : 0≤b) (hS : ∀ k∈S,(2:ℝ)^k≤b) :
    (∑ k∈S,(2:ℝ)^k) ≤ 2*b := by
  classical
  by_cases hne : S.Nonempty
  · let M := S.max' hne
    have hM k (hk : k∈S) : k≤M := Finset.le_max' S k hk
    let f := fun k : ℤ => (M-k).toNat
    have hinj : Set.InjOn f S := by
      intro k hk l hl h
      have hk' := Int.toNat_of_nonneg (sub_nonneg.mpr (hM k hk))
      have hl' := Int.toNat_of_nonneg (sub_nonneg.mpr (hM l hl))
      have := congrArg (fun n : ℕ => (n:ℤ)) h
      dsimp [f] at this
      omega
    have he k (hk : k∈S) : (2:ℝ)^k = (2:ℝ)^M*(1/2:ℝ)^(f k) := by
      have hk' := Int.toNat_of_nonneg (sub_nonneg.mpr (hM k hk))
      rw [one_div,inv_pow,← zpow_natCast]
      dsimp [f]
      rw [hk',← _root_.zpow_neg,← zpow_add₀ (by norm_num)]
      congr 1
      ring
    have hsum : (∑ k∈S,(1/2:ℝ)^(f k)) ≤ 2 := by
      rw [← Finset.sum_image hinj]
      have hs := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
      have hh := hs.summable.sum_le_tsum (S.image f) (fun n _ => by positivity)
      rw [hs.tsum_eq] at hh
      norm_num at hh
      exact hh
    calc
      _ = (2:ℝ)^M*∑ k∈S,(1/2:ℝ)^(f k) := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl he
      _ ≤ (2:ℝ)^M*2 := mul_le_mul_of_nonneg_left hsum (zpow_pos (by norm_num) _).le
      _ ≤ 2*b := by nlinarith [hS M (Finset.max'_mem S hne)]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

end EuclideanSteinitz.Filter

end

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def vectorMass (b : ι → ℝ) : ℝ := ∑ i,b i^2
noncomputable def eta (b : ι → ℝ) : ℝ := 1/(1+Real.sqrt (1-vectorMass b))
noncomputable def symmetricContraction (b : ι → ℝ) : Matrix ι ι ℝ := 1-eta b • vecMulVec b b
noncomputable def symmetricStep (b : ι → ℝ) (j : κ) : Step ι κ := ⟨symmetricContraction b,b,j⟩

omit [DecidableEq ι] in
lemma vectorMass_nonneg (b : ι → ℝ) : 0≤vectorMass b := Finset.sum_nonneg fun i _ => sq_nonneg (b i)
omit [DecidableEq ι] in
lemma eta_pos (b : ι → ℝ) : 0<eta b := div_pos (by norm_num) (by linarith [Real.sqrt_nonneg (1-vectorMass b)])
omit [DecidableEq ι] in
lemma eta_le_one (b : ι → ℝ) : eta b≤1 := by unfold eta; apply (div_le_one (by positivity)).mpr; linarith [Real.sqrt_nonneg (1-vectorMass b)]

omit [DecidableEq ι] in
lemma eta_identity {b : ι → ℝ} (hb : vectorMass b≤1) : 2*eta b-eta b^2*vectorMass b=1 := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hb)
  have hpos : 0<1+Real.sqrt (1-vectorMass b) := by positivity
  unfold eta
  field_simp
  nlinarith

omit [DecidableEq ι] in
lemma rank_square (b : ι → ℝ) : vecMulVec b b*vecMulVec b b=vectorMass b • vecMulVec b b := by
  ext i j
  simp only [Matrix.mul_apply,vecMulVec_apply,Matrix.smul_apply,smul_eq_mul,vectorMass]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma symmetricContraction_transpose (b : ι → ℝ) : (symmetricContraction b).transpose=symmetricContraction b := by
  simp [symmetricContraction]

lemma symmetricContraction_square {b : ι → ℝ} (hb : vectorMass b≤1) :
    symmetricContraction b*symmetricContraction b+vecMulVec b b=1 := by
  unfold symmetricContraction
  simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,Matrix.mul_smul,rank_square,smul_smul]
  have he := eta_identity hb
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  linear_combination -(vecMulVec b b i j) * he

lemma symmetricContraction_unit {b : ι → ℝ} (hb : vectorMass b<1) : IsUnit (symmetricContraction b) := by
  let t := eta b/(1-eta b*vectorMass b)
  have hd : 0<1-eta b*vectorMass b := by
    have h := mul_le_mul_of_nonneg_right (eta_le_one b) (vectorMass_nonneg b)
    linarith
  have ht : t-eta b-eta b*t*vectorMass b=0 := by
    dsimp [t]
    field_simp
    ring
  have hmul : symmetricContraction b*(1+t • vecMulVec b b)=1 := by
    unfold symmetricContraction
    simp only [Matrix.sub_mul,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,Matrix.mul_smul,rank_square,smul_smul]
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    linear_combination (vecMulVec b b i j) * ht
  have hmul' : (1+t • vecMulVec b b)*symmetricContraction b=1 := by
    have hh := congrArg Matrix.transpose hmul
    simpa only [Matrix.transpose_mul,symmetricContraction_transpose,Matrix.transpose_add,Matrix.transpose_one,
      Matrix.transpose_smul,Matrix.transpose_vecMulVec] using hh
  exact ⟨⟨symmetricContraction b,1+t • vecMulVec b b,hmul,hmul'⟩,rfl⟩

lemma symmetricStep_good {b : ι → ℝ} (hb : vectorMass b<1) (j : κ) : (symmetricStep b j).Good := by
  refine ⟨symmetricContraction_unit hb,?_⟩
  change symmetricContraction b*(symmetricContraction b).transpose+vecMulVec b b=1
  rw [symmetricContraction_transpose]
  exact symmetricContraction_square hb.le

lemma contraction_loss {b : ι → ℝ} (hb : vectorMass b≤1) (x : ι → ℝ) :
    vectorMass x-vectorMass (symmetricContraction b*ᵥx)=(b ⬝ᵥ x)^2 := by
  have he := symmetricContraction_square hb
  have ht := symmetricContraction_transpose b
  have hgram : (symmetricContraction b).transpose*symmetricContraction b=1-vecMulVec b b := by
    rw [ht,← he]; abel
  have hh := congrArg (fun A : Matrix ι ι ℝ => x ⬝ᵥ(A*ᵥx)) hgram
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,
    Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub,Matrix.vecMulVec_mulVec,dotProduct_smul,op_smul_eq_mul] at hh
  rw [dotProduct_comm x b] at hh
  simp only [dotProduct,← pow_two] at hh
  unfold vectorMass
  simp only [dotProduct]
  nlinarith [hh]

lemma contraction_apply (b x : ι → ℝ) :
    symmetricContraction b*ᵥx = x-(eta b*(b ⬝ᵥ x)) • b := by
  unfold symmetricContraction
  rw [Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,op_smul_eq_mul]
  ring

end EuclideanSteinitz.Filter

end

end OAI
