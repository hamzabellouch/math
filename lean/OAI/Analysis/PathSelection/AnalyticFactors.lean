import Mathlib
import OAI.Analysis.PathSelection.MonicFamilies
import OAI.Analysis.PathSelection.RootClusters
import OAI.Analysis.PathSelection.ScalarFields

namespace OAI

/-! Normal root limits and algebraic factorization of analytic scalar families. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Metric Filter Topology Complex
open scoped BigOperators Polynomial
namespace DegeneratingTrees

theorem analyticOrderAt_polynomial_eval (P : ℂ[X]) (hP : P ≠ 0) (a : ℂ) :
    analyticOrderAt P.eval a = (P.rootMultiplicity a : ℕ∞) := by
  obtain ⟨Q,hPQ,hQ⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP a
  apply (AnalyticOnNhd.eval_polynomial P a (mem_univ a)).analyticOrderAt_eq_natCast.mpr
  refine ⟨Q.eval,AnalyticOnNhd.eval_polynomial Q a (mem_univ a),?_,?_⟩
  · exact fun he => hQ (Polynomial.dvd_iff_isRoot.mpr he)
  · filter_upwards [] with z
    conv_lhs => rw [hPQ]
    simp

 

theorem analytic_polynomial_cluster {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (P : A → ℂ[X]) (hP : P 0 ≠ 0)
    (hF : AnalyticAt ℂ (fun x : A × ℂ => (P x.1).eval x.2) 0) :
    ∃ (U : Set A) (W : A → ℂ[X]), IsOpen U ∧ (0 : A) ∈ U ∧
      (∀ k, AnalyticOnNhd ℂ (fun q => (W q).coeff k) U) ∧
      ∀ q ∈ U, (W q).Monic ∧ (W q).natDegree = (P 0).rootMultiplicity 0 ∧ W q ∣ P q := by
  let d := (P 0).rootMultiplicity 0
  have hd : analyticOrderAt (fun y => (P (0 : A)).eval y) 0 = (d : ℕ∞) :=
    analyticOrderAt_polynomial_eval (P 0) hP 0
  obtain ⟨r,U,φ,hr,hU,h0,hFA,hφ,hφe,hφu,hm,hm0⟩ := fixed_circle_data hF hd
  let W : A → ℂ[X] := fun q => contourPolynomial (P q).eval r d
  refine ⟨U,W,hU,h0,?_,?_⟩
  · intro k q hq
    exact (analytic_contourPolynomial_coeff (F := fun x : A × ℂ => (P x.1).eval x.2)
      (r := r) (U := U) hm d k) q hq
  · intro q hq
    have hn (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : (P q).eval z ≠ 0 := by
      rw [← hφe q hq ⟨z,hz⟩]
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).mp (hφu q hq) ⟨z,hz⟩
    have hf : AnalyticOnNhd ℂ (P q).eval (closedBall 0 r) :=
      fun z _ => AnalyticOnNhd.eval_polynomial (P q) z (mem_univ z)
    obtain ⟨N,g,hN,hM,hD,hg,hgn,hEq⟩ := contour_fiber_factorization hr hf hn
    have hNd : N = d := by exact_mod_cast hN.symm.trans (hm0 q hq)
    subst N
    exact ⟨hM,hD,contourPolynomial_dvd hr hn (hm0 q hq)⟩

end DegeneratingTrees

 

 

 

open Set Metric Filter Topology Complex Polynomial
open scoped BigOperators
namespace DegeneratingTrees.ScalarEvaluation
variable {K α : Type*} [Field K] [Algebra ℂ K] {l : Filter α}
variable (e : ScalarEvaluation K α l)

lemma lift_monic_polynomial (hhol : e.HolomorphicallyClosed)
    {n m : ℕ} (a : Fin n → K) (c : Fin n → ℂ)
    (ha : ∀ i, Tendsto (e.value (a i)) l (𝓝 (c i)))
    (W : (Fin n → ℂ) → ℂ[X]) (hWa : ∀ k, AnalyticAt ℂ (fun q => (W q).coeff k) c)
    (hW : ∀ᶠ q in 𝓝 c, (W q).Monic ∧ (W q).natDegree = m) :
    ∃ V : K[X], V.Monic ∧ V.natDegree = m ∧
      e.polynomialValue V =ᶠ[l] fun x => W (fun i => e.value (a i) x) := by
  classical
  have hb : ∀ k : Fin m, ∃ b : K,
      e.value b =ᶠ[l] fun x => (W (fun i => e.value (a i) x)).coeff k := by
    intro k
    exact hhol n a c ha _ (hWa k)
  choose b hb using hb
  let V : K[X] := monicFamily b
  refine ⟨V,monicFamily_monic b,monicFamily_natDegree b,?_⟩
  have ht : Tendsto (fun x i => e.value (a i) x) l (𝓝 c) := tendsto_pi_nhds.mpr ha
  have hec : ∀ᶠ x in l, ∀ k : Fin (m+1),
      (e.polynomialValue V x).coeff k = e.value (V.coeff k) x :=
    Filter.eventually_all.mpr (fun k => e.polynomialValue_coeff_eventually V k)
  filter_upwards [Filter.eventually_all.mpr hb,ht.eventually hW,hec,e.one] with x hx hWx hcx hone
  ext k
  by_cases hk : k < m
  · rw [hcx ⟨k,by omega⟩]
    rw [show V.coeff k = b ⟨k,hk⟩ by simp [V,monicFamily_coeff,hk]]
    exact hx ⟨k,hk⟩
  · by_cases hkm : k = m
    · subst k
      rw [hcx ⟨m,by omega⟩,show V.coeff m = 1 by simp [V,monicFamily_coeff],hone]
      exact (hWx.2 ▸ hWx.1.coeff_natDegree).symm
    · have hmk : m < k := by omega
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (e.polynomialValue_natDegree_le V x) (by simpa [V,monicFamily_natDegree] using hmk)),
        coeff_eq_zero_of_natDegree_lt (by simpa [hWx.2] using hmk)]

 

lemma factor_of_finite_coeff_limits [NeBot l] (hhol : e.HolomorphicallyClosed)
    {P : K[X]} (hP : P.Monic) (c : Fin P.natDegree → ℂ)
    (hc : ∀ i : Fin P.natDegree, Tendsto (e.value (P.coeff i)) l (𝓝 (c i))) (a : ℂ) :
    ∃ V : K[X], V.Monic ∧ V.natDegree = (monicFamily c).rootMultiplicity a ∧ V ∣ P := by
  classical
  let d := P.natDegree
  let F : (Fin d → ℂ) → ℂ[X] := fun q =>
    (monicFamily (fun i => c i + q i)).comp (X + C a)
  have hF0 : F 0 ≠ 0 := by
    simpa [F,← taylor_apply] using (monicFamily_monic c).ne_zero
  have hFa : AnalyticAt ℂ (fun x : (Fin d → ℂ) × ℂ => (F x.1).eval x.2) 0 := by
    simpa [F,eval_comp] using monicFamily_eval_analytic c a
  obtain ⟨U,W,hU,h0,hWa,hW⟩ := analytic_polynomial_cluster F hF0 hFa
  let Z : (Fin d → ℂ) → ℂ[X] := fun q =>
    taylor (-a) (W (q-c))
  
  have hZa : ∀ k, AnalyticAt ℂ (fun q => (Z q).coeff k) c := by
    intro k
    
    have hma : ∀ j, AnalyticAt ℂ (fun q => (W (q-c)).coeff j) c := by
      intro j
      have h := (hWa j) 0 h0
      have ht : AnalyticAt ℂ (fun q : Fin d → ℂ => q-c) c := analyticAt_id.sub analyticAt_const
      exact h.comp_of_eq ht (by simp)
    have hUn : ∀ᶠ q in 𝓝 c, q-c ∈ U := by
      have ht : ContinuousAt (fun q : Fin d → ℂ => q-c) c := continuousAt_id.sub continuousAt_const
      exact ht.preimage_mem_nhds (by simpa using hU.mem_nhds h0)
    have hdW : ∀ᶠ q in 𝓝 c, (W (q-c)).natDegree < (F 0).rootMultiplicity 0 + 1 := by
      filter_upwards [hUn] with q hq
      rw [(hW _ hq).2.1]
      omega
    have hformula : (fun q => (Z q).coeff k) =ᶠ[𝓝 c]
        fun q => ∑ j ∈ Finset.range ((F 0).rootMultiplicity 0+1),
          (W (q-c)).coeff j * ((-a)^(j-k) * (j.choose k : ℂ)) := by
      filter_upwards [hdW] with q hq
      change (taylor (-a) (W (q-c))).coeff k = _
      conv_lhs => rw [← Polynomial.sum_monomial_eq (W (q-c))]
      simp only [Polynomial.sum_def,map_sum,taylor_monomial,finsetSum_coeff,coeff_C_mul,coeff_X_add_C_pow]
      apply Finset.sum_subset
      · intro j hj
        exact Finset.mem_range.mpr (lt_of_le_of_lt (le_natDegree_of_mem_supp j hj) hq)
      · intro j hj hjs
        simp [Polynomial.notMem_support_iff.mp hjs]
    exact (Finset.analyticAt_fun_sum _ (fun j hj => (hma j).mul analyticAt_const)).congr hformula.symm
  have hZ : ∀ᶠ q in 𝓝 c,
      (Z q).Monic ∧ (Z q).natDegree = (monicFamily c).rootMultiplicity a ∧
      Z q ∣ monicFamily q := by
    have ht : ContinuousAt (fun q : Fin d → ℂ => q-c) c := continuousAt_id.sub continuousAt_const
    have hu : ∀ᶠ q in 𝓝 c, q-c ∈ U := ht.preimage_mem_nhds (by simpa using hU.mem_nhds h0)
    filter_upwards [hu] with q hq
    obtain ⟨hm,hd,hdiv⟩ := hW (q-c) hq
    have he : F (q-c) = taylor a (monicFamily q) := by
      simp [F,taylor_apply,Pi.sub_apply]
    have hr : (F 0).rootMultiplicity 0 = (monicFamily c).rootMultiplicity a := by
      simpa [F] using (Polynomial.rootMultiplicity_eq_rootMultiplicity (p := monicFamily c) (t := a)).symm
    refine ⟨by simpa [Z,Monic] using hm,by simpa [Z,hr] using hd,?_⟩
    have hv := (Polynomial.taylorEquiv (-a)).toRingHom.map_dvd hdiv
    change taylor (-a) (W (q-c)) ∣ taylor (-a) (F (q-c)) at hv
    simpa [Z,he,Polynomial.taylor_taylor] using hv
  obtain ⟨V,hVm,hVd,hVe⟩ := e.lift_monic_polynomial hhol (fun i : Fin d => P.coeff i) c hc Z hZa
    (hZ.mono (fun q hq => ⟨hq.1,hq.2.1⟩))
  refine ⟨V,hVm,hVd,e.polynomial_dvd_of_eventually hVm ?_⟩
  have ht : Tendsto (fun x i => e.value (P.coeff (i : Fin d)) x) l (𝓝 c) := tendsto_pi_nhds.mpr hc
  have hPfun : e.polynomialValue P =ᶠ[l]
      fun x => monicFamily (fun i : Fin d => e.value (P.coeff i) x) := by
    
    have hEc : ∀ᶠ x in l, ∀ k : Fin (d+1),
        (e.polynomialValue P x).coeff k = e.value (P.coeff k) x :=
      Filter.eventually_all.mpr (fun k => e.polynomialValue_coeff_eventually P k)
    filter_upwards [hEc,e.one] with x hx h1
    ext k
    rw [monicFamily_coeff]
    split_ifs with hk hkD
    · exact hx ⟨k,by omega⟩
    · subst k
      rw [hx ⟨d,by omega⟩,hP.coeff_natDegree,h1]
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (e.polynomialValue_natDegree_le P x) (by dsimp [d] at *; omega))
  filter_upwards [hVe,ht.eventually hZ,hPfun] with x hx hz hp
  simpa [hx,hp] using hz.2.2

end DegeneratingTrees.ScalarEvaluation

 

 

open Set Filter Topology Complex Polynomial
open scoped BigOperators
namespace DegeneratingTrees

lemma proper_root_cluster {P : ℂ[X]} (hP : P.Monic) (hd : 0 < P.natDegree)
    (hdep : P.coeff (P.natDegree-1) = 0) (hpow : P ≠ X^P.natDegree) :
    ∃ a : ℂ, 0 < P.rootMultiplicity a ∧ P.rootMultiplicity a < P.natDegree := by
  obtain ⟨a,ha⟩ := Complex.exists_root (natDegree_pos_iff_degree_pos.mp hd)
  have hmpos : 0 < P.rootMultiplicity a := (rootMultiplicity_pos hP.ne_zero).mpr ha
  have hmdvd := pow_rootMultiplicity_dvd P a
  have hmle : P.rootMultiplicity a ≤ P.natDegree := by
    simpa using natDegree_le_of_dvd hmdvd hP.ne_zero
  refine ⟨a,hmpos,lt_of_le_of_ne hmle ?_⟩
  intro heq
  have he : P = (X-C a)^P.natDegree := by
    have hp := eq_of_monic_of_dvd_of_natDegree_le ((monic_X_sub_C a).pow (P.rootMultiplicity a))
      hP hmdvd (by simp [heq])
    simpa [heq] using hp
  have hcoeff : P.coeff (P.natDegree-1) = (-a) * (P.natDegree : ℂ) := by
    conv_lhs => arg 1; rw [he]
    rw [sub_eq_add_neg,← C_neg,coeff_X_add_C_pow]
    have hsub : P.natDegree - (P.natDegree-1) = 1 := by omega
    have hchoose : P.natDegree.choose (P.natDegree-1) = P.natDegree := by
      obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
      rw [hn]
      simp
    rw [hsub,hchoose,pow_one]
  have ha0 : a = 0 := by
    have hn : (P.natDegree : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
    rw [hdep] at hcoeff
    exact neg_eq_zero.mp ((mul_eq_zero.mp hcoeff.symm).resolve_right hn)
  apply hpow
  simpa [ha0] using he

lemma rescale_monic_eq {K : Type*} [Field K] {P : K[X]} (hP : P.Monic)
    (ρ : K) (hρ : ρ ≠ 0) :
    monicFamily (fun i : Fin P.natDegree => P.coeff i / ρ^(P.natDegree-i.val)) =
      C (ρ^P.natDegree)⁻¹ * P.comp (C ρ * X) := by
  ext k
  rw [monicFamily_coeff,coeff_C_mul,comp_C_mul_X_coeff]
  split_ifs with hk hkd
  · dsimp only
    rw [show ρ^P.natDegree = ρ^k * ρ^(P.natDegree-k) by
      rw [← pow_add,Nat.add_sub_of_le hk.le]]
    field_simp
  · subst k
    rw [hP.coeff_natDegree,one_mul]
    exact (inv_mul_cancel₀ (pow_ne_zero _ hρ)).symm
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),zero_mul,mul_zero]

lemma rescale_monic_irreducible {K : Type*} [Field K] {P : K[X]} (hP : P.Monic)
    (hI : Irreducible P) (ρ : K) (hρ : ρ ≠ 0) :
    Irreducible (monicFamily (fun i : Fin P.natDegree => P.coeff i / ρ^(P.natDegree-i.val))) := by
  let : Invertible ρ := invertibleOfNonzero hρ
  rw [rescale_monic_eq hP ρ hρ]
  apply (irreducible_isUnit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hρ))))).mpr
  have h := hI.map (algEquivCMulXAddC ρ 0)
  simpa [algEquivCMulXAddC_apply,← comp_eq_aeval] using h

lemma irreducible_no_proper_monic_factor {K : Type*} [Field K] {P V : K[X]}
    (hI : Irreducible P) (hV : V.Monic) (hdiv : V ∣ P)
    (hpos : 0 < V.natDegree) (hsmall : V.natDegree < P.natDegree) : False := by
  obtain ⟨Q,rfl⟩ := hdiv
  rcases hI.isUnit_or_isUnit rfl with hv | hq
  · have hdeg := natDegree_eq_zero_of_isUnit hv
    omega
  · have hq0 : Q ≠ 0 := hq.ne_zero
    have hdeg := hV.natDegree_mul' hq0
    rw [natDegree_eq_zero_of_isUnit hq,Nat.add_zero] at hdeg
    omega

end DegeneratingTrees
end

end OAI
