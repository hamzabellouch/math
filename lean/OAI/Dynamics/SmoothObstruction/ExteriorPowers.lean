import Mathlib

namespace OAI

section

open scoped ContDiff BigOperators
open Module

namespace SmoothObstruction.ExteriorStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The exterior power as a continuous operator on the canonical inner product space. -/
noncomputable def exterior (p : ℕ) (A : E →L[ℝ] E) :
    (⋀[ℝ]^p E) →L[ℝ] (⋀[ℝ]^p E) :=
  (exteriorPower.map p A.toLinearMap).toContinuousLinearMap

@[simp] theorem exterior_apply (p : ℕ) (A : E →L[ℝ] E) (v : ⋀[ℝ]^p E) :
    exterior p A v = exteriorPower.map p A.toLinearMap v := rfl

/-- A determinant polynomial is smooth in all its entries. -/
theorem contDiff_det {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : WithTop ℕ∞}
    (f : D → Matrix ι ι ℝ) (hf : ∀ i j, ContDiff ℝ n (fun x => f x i j)) :
    ContDiff ℝ n (fun x => (f x).det) := by
  simp only [Matrix.det_apply]
  fun_prop

/-- The canonical wedge of a fixed number of vectors is a smooth polynomial. -/
theorem contDiff_wedge (p : ℕ) :
    ContDiff ℝ ∞ (exteriorPower.ιMulti ℝ p (M := E)) := by
  let b := (stdOrthonormalBasis ℝ E).toBasis
  let e := (b.exteriorPower p).equivFunL
  apply e.comp_contDiff_iff.mp
  apply contDiff_pi.mpr
  intro s
  change ContDiff ℝ ∞ (fun v => (b.exteriorPower p).repr (exteriorPower.ιMulti ℝ p v) s)
  simp only [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  apply contDiff_det
  intro i j
  exact ((b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j)).toContinuousLinearMap.contDiff).comp
    (contDiff_apply ℝ E i)

/-- Exterior powers depend smoothly on the input operator. -/
theorem contDiff_exterior (p : ℕ) :
    ContDiff ℝ ∞ (exterior (E := E) p) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  have hv : v ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ p (M := E))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, rfl⟩ := hv
    simp only [exterior_apply, exteriorPower.map_apply_ιMulti]
    apply (contDiff_wedge p).comp
    exact contDiff_pi.mpr fun i => contDiff_id.clm_apply contDiff_const
  | zero => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : E →L[ℝ] E => (0 : ⋀[ℝ]^p E)))
  | add x y hx hy ihx ihy => simpa only [map_add] using ihx.add ihy
  | smul a x hx ih => simpa only [map_smul] using ih.const_smul a

/-- A uniform one-step exterior error on every bounded operator ball. -/
theorem exists_exterior_lipschitz (p : ℕ) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : E →L[ℝ] E),
      ‖A‖ ≤ K → ‖B - A‖ ≤ 1 →
      ‖exterior p B - exterior p A‖ ≤ C * ‖B - A‖ := by
  obtain ⟨C, hC⟩ := (contDiff_exterior (E := E) p).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall (0 : E →L[ℝ] E) (K + 1)) (isCompact_closedBall 0 (K + 1))
  refine ⟨C, C.coe_nonneg, fun A B hA hBA => ?_⟩
  have hB : ‖B‖ ≤ K + 1 := by
    calc
      ‖B‖ = ‖(B - A) + A‖ := by rw [sub_add_cancel]
      _ ≤ ‖B - A‖ + ‖A‖ := norm_add_le _ _
      _ ≤ K + 1 := by linarith
  have hAmem : A ∈ Metric.closedBall (0 : E →L[ℝ] E) (K + 1) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hA.trans (by linarith)
  have hBmem : B ∈ Metric.closedBall (0 : E →L[ℝ] E) (K + 1) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hB
  simpa only [dist_eq_norm] using hC.dist_le_mul B hBmem A hAmem

@[simp] theorem exterior_one (p : ℕ) :
    exterior (E := E) p 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  change exteriorPower.map p LinearMap.id v = v
  rw [exteriorPower.map_id]
  rfl

@[simp] theorem exterior_mul (p : ℕ) (A B : E →L[ℝ] E) :
    exterior p (A * B) = exterior p A * exterior p B := by
  apply ContinuousLinearMap.ext
  intro v
  change exteriorPower.map p (A.toLinearMap.comp B.toLinearMap) v =
    exteriorPower.map p A.toLinearMap (exteriorPower.map p B.toLinearMap v)
  rw [exteriorPower.map_comp]
  rfl

/-- The same one-step constant works for every exterior degree up to `d`. -/
theorem exists_uniform_exterior_lipschitz (d : ℕ) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ), p ≤ d → ∀ (A B : E →L[ℝ] E),
      ‖A‖ ≤ K → ‖B - A‖ ≤ 1 →
      ‖exterior p B - exterior p A‖ ≤ C * ‖B - A‖ := by
  choose C hCpos hC using fun p : Fin (d + 1) => exists_exterior_lipschitz (E := E) p.val K
  refine ⟨∑ p, C p, Finset.sum_nonneg (fun p _ => hCpos p), ?_⟩
  intro p hp A B hA hBA
  let q : Fin (d + 1) := ⟨p, by omega⟩
  have hle : C q ≤ ∑ i, C i := Finset.single_le_sum (fun i _ => hCpos i) (Finset.mem_univ q)
  exact (hC q A B hA hBA).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exterior_smul (p : ℕ) (c : ℝ) (A : E →L[ℝ] E) :
    exterior p (c • A)=c^p • exterior p A := by
  apply ContinuousLinearMap.coe_injective
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorPower.map p (c • A).toLinearMap (exteriorPower.ιMulti ℝ p v) =
    c^p • exteriorPower.map p A.toLinearMap (exteriorPower.ιMulti ℝ p v)
  simp only [exteriorPower.map_apply_ιMulti,Function.comp_def,
    ContinuousLinearMap.coe_coe,smul_apply]
  simpa using (exteriorPower.ιMulti ℝ p (M:=E)).map_smul_univ (fun _ => c) (fun i => A (v i))

/-- A fixed dimensional polynomial bound sufficient to absorb changes of
gauge into the source's exp(Cbn) factor, with exterior degree zero included. -/
theorem exists_power_bound (p : ℕ) : ∃ C : ℝ,1≤C ∧ ∀ A : E →L[ℝ] E,
    ‖exterior p A‖≤C*(max 1 ‖A‖)^p := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) 1).exists_bound_of_continuousOn
    (f:=exterior (E:=E) p) (contDiff_exterior p).continuous.continuousOn
  refine ⟨max C 1,le_max_right _ _,?_⟩
  intro A
  let r := max 1 ‖A‖
  have hr : 0<r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hAr : ‖r⁻¹ • A‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).mpr (by simpa only [mul_one] using le_max_right (1:ℝ) ‖A‖)
  have ha := hC (r⁻¹ • A) (by simpa only [mem_closedBall,dist_zero_right] using hAr)
  have he : A=r • (r⁻¹ • A) := by rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  calc
    _ = ‖r^p • exterior p (r⁻¹ • A)‖ := by
      congr 1
      conv_lhs => rw [he,exterior_smul]
    _ ≤ r^p*‖exterior p (r⁻¹ • A)‖ := by
      simpa only [Real.norm_eq_abs,abs_of_pos (pow_pos hr p)] using
        ContinuousLinearMap.opNorm_smul_le (r^p) (exterior p (r⁻¹ • A))
    _ ≤ r^p*(max C 1) := mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (pow_nonneg hr.le p)
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- A convenient basis norm bound; no singular-value theorem is needed. -/
lemma norm_le_sum_basis (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    ‖T‖≤∑ i,‖T (b i)‖ := by
  classical
  apply T.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have hrepr : x=∑ i,(b.repr x i) • b i := (b.sum_repr x).symm
  calc
    ‖T x‖ = ‖∑ i,(b.repr x i) • T (b i)‖ := by
      conv_lhs => rw [hrepr]
      simp only [map_sum,map_smul]
    _ ≤ ∑ i,‖(b.repr x i) • T (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ i,‖x‖*‖T (b i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,b.repr_apply_apply]
      have hh := norm_inner_le_norm (𝕜:=ℝ) (b i) x
      rw [b.norm_eq_one,one_mul] at hh
      exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ = _ := by rw [←Finset.mul_sum]; ring

variable [LinearOrder ι]

lemma exterior_eigen_basis (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (T : E →L[ℝ] E) (a : ι → ℝ) (ha : ∀ i,T (b i)=a i • b i)
    (s : powersetCard ι p) : exterior p T ((b.exteriorPower p) s)=
      (∏ i : Fin p,a (powersetCard.ofFinEmbEquiv.symm s i)) • ((b.exteriorPower p) s) := by
  have hb : (b.exteriorPower p) s=exteriorPower.ιMulti ℝ p
      (fun i => b (powersetCard.ofFinEmbEquiv.symm s i)) := by
    change (b.exteriorPower p).toBasis s=_
    rw [b.toBasis_exteriorPower,exteriorPower.coe_basis]
    rfl
  rw [hb,exterior_apply,exteriorPower.map_apply_ιMulti]
  simp only [Function.comp_def,ContinuousLinearMap.coe_coe,ha]
  exact (exteriorPower.ιMulti ℝ p (M:=E)).map_smul_univ _ _

/-- The complete exterior product estimate in a diagonal gauge depends on
the SUM of selected rates, not on a coarser maximum single rate. -/
lemma exterior_diagonal_bound (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (T : E →L[ℝ] E) (a : ι → ℝ) (ha : ∀ i,T (b i)=a i • b i)
    {K : ℝ} (hK : ∀ s : powersetCard ι p,
      |∏ i : Fin p,a (powersetCard.ofFinEmbEquiv.symm s i)|≤K) :
    ‖exterior p T‖≤(Fintype.card (powersetCard ι p):ℝ)*K := by
  apply (norm_le_sum_basis (b.exteriorPower p) (exterior p T)).trans
  calc
    _ ≤ ∑ _s : powersetCard ι p,K := by
      apply Finset.sum_le_sum
      intro s _
      rw [exterior_eigen_basis b p T a ha s,norm_smul,(b.exteriorPower p).norm_eq_one,mul_one,Real.norm_eq_abs]
      exact hK s
    _ = _ := by simp
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

lemma exterior_eigen_lower (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (D : E →L[ℝ] E) (a : ι → ℝ) (ha : ∀ i,D (b i)=a i • b i)
    (s : powersetCard ι p) :
    |∏ i : Fin p,a (powersetCard.ofFinEmbEquiv.symm s i)|≤‖exterior p D‖ := by
  have h := (exterior p D).le_opNorm ((b.exteriorPower p) s)
  rw [exterior_eigen_basis b p D a ha s,norm_smul,
    (b.exteriorPower p).norm_eq_one,mul_one,mul_one,Real.norm_eq_abs] at h
  exact h

omit [Fintype ι] in
lemma eigen_exp_product (p : ℕ) (lam : ι → ℝ) (l : ℝ) (s : powersetCard ι p) :
    (∏ i : Fin p,Real.exp (l*lam (powersetCard.ofFinEmbEquiv.symm s i))) =
      Real.exp (l*∑ i : Fin p,lam (powersetCard.ofFinEmbEquiv.symm s i)) := by
  rw [Finset.mul_sum,Real.exp_sum]

lemma exterior_rate_upper (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (D : E →L[ℝ] E) (lam : ι → ℝ) {l Λ : ℝ} (hl : 0≤l)
    (ha : ∀ i,D (b i)=Real.exp (l*lam i) • b i)
    (hm : ∀ s : powersetCard ι p,∑ i : Fin p,lam (powersetCard.ofFinEmbEquiv.symm s i)≤Λ) :
    ‖exterior p D‖≤(Fintype.card (powersetCard ι p):ℝ)*Real.exp (l*Λ) := by
  apply exterior_diagonal_bound b p D _ ha
  intro s
  rw [eigen_exp_product,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hm s) hl)

/-- An explicit subinterval exterior bound after changing a finite gauge.
This allows negative Λ, so that it is suitable for relative minor transfer. -/
theorem exterior_gauge_bound (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (U V D : E →L[ℝ] E) (lam : ι → ℝ) {l Λ G C : ℝ}
    (hl : 0≤l) (hG : 1≤G) (hC : 0≤C)
    (hpoly : ∀ A : E →L[ℝ] E,‖exterior p A‖≤C*(max 1 ‖A‖)^p)
    (hU : ‖U‖≤G) (hV : ‖V‖≤G)
    (ha : ∀ i,D (b i)=Real.exp (l*lam i) • b i)
    (hm : ∀ s : powersetCard ι p,∑ i : Fin p,lam (powersetCard.ofFinEmbEquiv.symm s i)≤Λ) :
    ‖exterior p (U*D*V)‖≤C^2*G^(2*p)*
      (Fintype.card (powersetCard ι p):ℝ)*Real.exp (l*Λ) := by
  have hGU : ‖exterior p U‖≤C*G^p := (hpoly U).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (max_le hG hU) p) hC)
  have hGV : ‖exterior p V‖≤C*G^p := (hpoly V).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (max_le hG hV) p) hC)
  have hD := exterior_rate_upper b p D lam hl ha hm
  rw [exterior_mul,exterior_mul]
  calc
    _ ≤ ‖exterior p U‖*‖exterior p D‖*‖exterior p V‖ :=
      (ContinuousLinearMap.opNorm_comp_le (exterior p U * exterior p D) (exterior p V)).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le (exterior p U) (exterior p D))
          (ContinuousLinearMap.opNorm_nonneg _))
    _ ≤ (C*G^p)*((Fintype.card (powersetCard ι p):ℝ)*Real.exp (l*Λ))*(C*G^p) := by
      apply mul_le_mul (mul_le_mul hGU hD (ContinuousLinearMap.opNorm_nonneg _) (by positivity)) hGV
        (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    _ = _ := by rw [show 2*p=p+p by omega,pow_add]; ring

/-- The fast determinant line has the exact sum rate before either endpoint
change of gauge. This is the genuine volume-line lower input. -/
lemma gauge_line_preimage_lower (p : ℕ) (U V P D : E →L[ℝ] E)
    (hdiag : D=V*P*U) {a K : ℝ}
    (hV : ‖exterior p V‖≤K)
    (v : (⋀[ℝ]^p E)) (hv : exterior p D v=a • v) :
    |a| *‖v‖≤K*‖exterior p P (exterior p U v)‖ := by
  have he : exterior p D v=exterior p V (exterior p P (exterior p U v)) := by
    rw [hdiag,exterior_mul,exterior_mul]
    rfl
  have hn := (exterior p V).le_opNorm (exterior p P (exterior p U v))
  rw [←he,hv,norm_smul,Real.norm_eq_abs] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hV (norm_nonneg _))

lemma gauge_line_lower (p : ℕ) (U V P D : E →L[ℝ] E)
    (hdiag : D=V*P*U) {a K : ℝ} (hK : 0≤K)
    (hU : ‖exterior p U‖≤K) (hV : ‖exterior p V‖≤K)
    (v : (⋀[ℝ]^p E)) (hv : exterior p D v=a • v) :
    |a| *‖exterior p U v‖≤K^2*‖exterior p P (exterior p U v)‖ := by
  have hU' := ((exterior p U).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hU (norm_nonneg _))
  have hP := gauge_line_preimage_lower p U V P D hdiag hV v hv
  calc
    _ ≤ |a| *(K*‖v‖) := mul_le_mul_of_nonneg_left hU' (abs_nonneg _)
    _ = K*(|a| *‖v‖) := by ring
    _ ≤ K*(K*‖exterior p P (exterior p U v)‖) := mul_le_mul_of_nonneg_left hP hK
    _ = _ := by ring

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [FiniteDimensional ℝ E] [LinearOrder ι] in
lemma diagonal_apply_complement (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E)
    (a : ι → ℝ) (ha : ∀ i,T (b i)=a i • b i) (s : ι) {K : ℝ} (hK : 0≤K)
    (hother : ∀ i,i≠s→|a i|≤K) (x : E) (hx : b.repr x s=0) :
    ‖T x‖≤(Fintype.card ι:ℝ)*K*‖x‖ := by
  classical
  have hexp : T x=∑ i,(b.repr x i) • T (b i) := by
    conv_lhs => rw [←b.sum_repr x]
    simp only [map_sum,map_smul]
  rw [hexp]
  calc
    _ ≤ ∑ i,‖(b.repr x i) • T (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι,‖x‖*K := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i=s
      · subst i
        rw [hx,zero_smul,norm_zero]
        positivity
      · rw [ha,norm_smul,norm_smul,b.norm_eq_one,mul_one,Real.norm_eq_abs]
        have hb : ‖b.repr x i‖≤‖x‖ := by
          rw [b.repr_apply_apply]
          simpa only [b.norm_eq_one,one_mul] using norm_inner_le_norm (𝕜:=ℝ) (b i) x
        exact mul_le_mul hb (hother i hi) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

lemma wedge_leading_zero (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (v : Fin p → E) (i₀ : Fin p)
    (hz : ∀ j : Fin p,b.repr (v i₀) (powersetCard.ofFinEmbEquiv.symm s j)=0) :
    (b.exteriorPower p).repr (exteriorPower.ιMulti ℝ p v) s=0 := by
  change (b.exteriorPower p).toBasis.repr (exteriorPower.ιMulti ℝ p v) s=0
  rw [b.toBasis_exteriorPower,exteriorPower.basis_repr_apply,exteriorPower.ιMultiDual_apply_ιMulti]
  apply Matrix.det_eq_zero_of_row_eq_zero i₀
  intro j
  exact hz j

/-- A dimensional wedge constant, derived from continuity, not assumed. -/
theorem exists_wedge_bound (p : ℕ) : ∃ W : ℝ,0≤W ∧ ∀ v : Fin p → E,
    ‖exteriorPower.ιMulti ℝ p v‖≤W*∏ i,‖v i‖ := by
  let f : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) (⋀[ℝ]^p E) :=
    ⟨(exteriorPower.ιMulti ℝ p (M:=E)).toMultilinearMap,(contDiff_wedge p).continuous⟩
  exact ⟨‖f‖,ContinuousMultilinearMap.opNorm_nonneg f,fun v => f.le_opNorm v⟩

/-- Nonleading p-minors, in the actual changed gauge, retain the full two-gap
loss. The vanishing leading coefficient is proved from one slow vector. -/
theorem mixed_exterior_bound (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (U D V : E →L[ℝ] E) (a : ι → ℝ)
    (ha : ∀ i,D (b i)=a i • b i) {C G K W : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hW : 0≤W)
    (hU : ‖exterior p U‖≤C) (hV : ‖V‖≤G)
    (hWb : ∀ v : Fin p → E,‖exteriorPower.ιMulti ℝ p v‖≤W*∏ i,‖v i‖)
    (hr : ∀ t : powersetCard ι p,t≠s→
      |∏ i : Fin p,a (powersetCard.ofFinEmbEquiv.symm t i)|≤K)
    (v : Fin p → E) (i₀ : Fin p)
    (hz : ∀ j : Fin p,b.repr (V (v i₀)) (powersetCard.ofFinEmbEquiv.symm s j)=0) :
    ‖exteriorPower.ιMulti ℝ p (fun i => (U*D*V) (v i))‖≤
      C*(Fintype.card (powersetCard ι p):ℝ)*K*W*G^p*(∏ i,‖v i‖) := by
  let w := exteriorPower.ιMulti ℝ p (fun i => V (v i))
  have hw : (b.exteriorPower p).repr w s=0 := wedge_leading_zero b p s _ i₀ hz
  have hD : ‖exterior p D w‖≤(Fintype.card (powersetCard ι p):ℝ)*K*‖w‖ :=
    diagonal_apply_complement (b.exteriorPower p) (exterior p D)
      (fun t => ∏ i : Fin p,a (powersetCard.ofFinEmbEquiv.symm t i))
      (exterior_eigen_basis b p D a ha) s hK hr w hw
  have hvb : (∏ i,‖V (v i)‖)≤G^p*(∏ i,‖v i‖) := by
    calc
      _ ≤ ∏ i : Fin p,G*‖v i‖ := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => (V.le_opNorm (v i)).trans (mul_le_mul_of_nonneg_right hV (norm_nonneg _)))
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hwb : ‖w‖≤W*(G^p*(∏ i,‖v i‖)) :=
    (hWb _).trans (mul_le_mul_of_nonneg_left hvb hW)
  have he : exteriorPower.ιMulti ℝ p (fun i => (U*D*V) (v i))=exterior p U (exterior p D w) := by
    simp only [w,exterior_apply,exteriorPower.map_apply_ιMulti,Function.comp_def]
    rfl
  rw [he]
  calc
    _ ≤ ‖exterior p U‖*‖exterior p D w‖ := (exterior p U).le_opNorm _
    _ ≤ C*((Fintype.card (powersetCard ι p):ℝ)*K*‖w‖) :=
      mul_le_mul hU hD (norm_nonneg _) hC
    _ ≤ C*((Fintype.card (powersetCard ι p):ℝ)*K*(W*(G^p*(∏ i,‖v i‖)))) := by
      gcongr
    _ = _ := by ring
end SmoothObstruction.ExteriorStability

end

section

namespace SmoothObstruction.RateSums
open Finset
variable {ι : Type*} [DecidableEq ι]

lemma sdiff_card_eq {S F : Finset ι} (hcard : S.card=F.card) :
    (S\F).card=(F\S).card := by
  have hS := card_sdiff_add_card_inter S F
  have hF := card_sdiff_add_card_inter F S
  rw [inter_comm F S] at hF
  omega

/-- Every nonfast minor of maximal fast degree loses at least two gap units.
Nothing here requires positive fast rates or negative slow rates. -/
theorem strict_rate_sum_gap (lam : ι → ℝ) (F S : Finset ι)
    {γ g : ℝ} (hg : 0≤g) (hcard : S.card=F.card) (hne : S≠F)
    (hf : ∀ j∈F,γ+g≤lam j) (hs : ∀ j∉F,lam j≤γ-g) :
    ∑ j∈S,lam j ≤ (∑ j∈F,lam j)-2*g := by
  have hc : (S\F).card=(F\S).card := sdiff_card_eq hcard
  have hnon : (S\F).Nonempty := by
    by_contra hh
    have hempty := not_nonempty_iff_eq_empty.mp hh
    have hsub := sdiff_eq_empty_iff_subset.mp hempty
    exact hne (eq_of_subset_of_card_le hsub (by omega))
  have hcp : 1≤((S\F).card:ℝ) := by
    exact_mod_cast hnon.card_pos
  have hslow : ∑ j∈S\F,lam j≤(S\F).card*(γ-g) := by
    calc
      _ ≤ ∑ _j∈S\F,(γ-g) := sum_le_sum fun j hj => hs j (mem_sdiff.mp hj).2
      _ = _ := by simp; ring
  have hfast : (S\F).card*(γ+g)≤∑ j∈F\S,lam j := by
    rw [hc]
    calc
      _ = ∑ _j∈F\S,(γ+g) := by simp; ring
      _ ≤ _ := sum_le_sum fun j hj => hf j (mem_sdiff.mp hj).1
  have hS := sum_sdiff (s₁:=S∩F) (s₂:=S) (inter_subset_left) (f:=lam)
  have hF := sum_sdiff (s₁:=S∩F) (s₂:=F) (inter_subset_right) (f:=lam)
  have hdS : S\(S∩F)=S\F := by ext j; simp
  have hdF : F\(S∩F)=F\S := by ext j; simp
  rw [hdS] at hS
  rw [hdF] at hF
  nlinarith [mul_nonneg (sub_nonneg.mpr hcp) hg]

theorem rate_sum_max (lam : ι → ℝ) (F S : Finset ι)
    {γ g : ℝ} (hg : 0≤g) (hcard : S.card=F.card)
    (hf : ∀ j∈F,γ+g≤lam j) (hs : ∀ j∉F,lam j≤γ-g) :
    ∑ j∈S,lam j ≤ ∑ j∈F,lam j := by
  by_cases he : S=F
  · simp [he]
  · exact (strict_rate_sum_gap lam F S hg hcard he hf hs).trans (by linarith)
end SmoothObstruction.RateSums

end

end OAI
