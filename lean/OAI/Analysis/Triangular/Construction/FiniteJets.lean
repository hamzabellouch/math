import OAI.Analysis.Triangular.Certificate.WaveIntervals

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction
open Complex

lemma sineFactor_deriv (a : Fin 15) : deriv (sineFactor a) =
    fun s => 2*(kappa:ℂ)*cos ((kappa:ℂ)*(s-(residue a:ℂ))) := by
  funext s
  have hh := ((((hasDerivAt_id s).sub_const (residue a:ℂ)).const_mul
    (kappa:ℂ)).csin.const_mul 2).deriv
  change deriv (fun y => 2*sin ((kappa:ℂ)*(y-(residue a:ℂ)))) s = _
  simpa only [id_eq,mul_one,mul_assoc,mul_comm,mul_left_comm] using hh
lemma sineFactor_second (a : Fin 15) : iteratedDeriv 2 (sineFactor a) =
    fun s => -(kappa:ℂ)^2*sineFactor a s := by
  rw [show 2 = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,sineFactor_deriv]
  funext s
  have hh := ((((hasDerivAt_id s).sub_const (residue a:ℂ)).const_mul
    (kappa:ℂ)).ccos.const_mul (2*(kappa:ℂ))).deriv
  convert hh using 1 <;> simp only [sineFactor,id_eq,mul_one]
  ring

lemma square_zero_jets (f : ℂ → ℂ) (hf : Differentiable ℂ f) (n : ℂ)
    (h0 : f n=0) (h2 : iteratedDeriv 2 f n=0) :
    iteratedDeriv 0 (fun s => f s*f s) n=0 ∧
    iteratedDeriv 1 (fun s => f s*f s) n=0 ∧
    iteratedDeriv 2 (fun s => f s*f s) n=2*(deriv f n)^2 ∧
    iteratedDeriv 3 (fun s => f s*f s) n=0 := by
  constructor
  · simp [iteratedDeriv_zero,h0]
  constructor
  · rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hf.contDiff.contDiffAt]
    simp [Finset.sum_range_succ,iteratedDeriv_zero,h0]
  constructor
  · rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hf.contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one,h0,h2]
    ring
  · rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hf.contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one,h0,h2]

lemma square_zero_product_jets (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (n : ℂ) (h0 : f n=0) (h2 : iteratedDeriv 2 f n=0) :
    iteratedDeriv 2 (fun s => f s^2*g s) n=2*(deriv f n)^2*g n ∧
    iteratedDeriv 3 (fun s => f s^2*g s) n=6*(deriv f n)^2*deriv g n := by
  obtain ⟨hj0,hj1,hj2,hj3⟩ := square_zero_jets f hf n h0 h2
  have hh : (fun s => f s^2) = (fun s => f s*f s) := by funext s; ring
  have hd : Differentiable ℂ (fun s => f s^2) := hf.pow 2
  constructor
  · rw [iteratedDeriv_fun_mul hd.contDiff.contDiffAt hg.contDiff.contDiffAt,hh]
    norm_num [Finset.sum_range_succ,hj0,hj1,hj2,iteratedDeriv_zero]
  · rw [iteratedDeriv_fun_mul hd.contDiff.contDiffAt hg.contDiff.contDiffAt,hh]
    norm_num [Finset.sum_range_succ,hj0,hj1,hj2,hj3,iteratedDeriv_one]
    ring_nf
    simp

lemma sineFactor_at_residue (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    sineFactor a n=0 := by
  have he : (kappa:ℂ)*((n:ℂ)-(residue a:ℂ))=(n/36:ℤ)*(Real.pi:ℂ) := by
    have hh := congrArg (fun z : ℤ => (z:ℂ)) (Int.emod_add_mul_ediv n 36)
    rw [hn] at hh
    push_cast at hh
    unfold kappa
    push_cast
    linear_combination -(Real.pi:ℂ)/36*hh
  unfold sineFactor
  rw [he]
  have hz := congrArg Complex.ofReal (Real.sin_int_mul_pi (n/36))
  have hh : Complex.sin ((n/36:ℤ)*(Real.pi:ℂ))=0 := by
    simpa only [Complex.ofReal_zero,Complex.ofReal_sin,Complex.ofReal_mul,Complex.ofReal_intCast] using hz
  simp [hh]

lemma finiteC_matching_jets (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    (finiteC a n).re=Q n ∧ 6*(deriv (finiteC a) n).re=(waveDerivative 3 n).re := by
  let g : ℂ → ℂ := fun s => ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2
  have hf : Differentiable ℂ (sineFactor a) := by unfold sineFactor; fun_prop
  have hg : Differentiable ℂ g := by unfold g sineFactor; fun_prop
  have h0 := sineFactor_at_residue a n hn
  have h2 : iteratedDeriv 2 (sineFactor a) n=0 := by simp only [sineFactor_second,h0,mul_zero]
  have hc : cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2=1 := by
    have hsin : sin ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))=0 := by
      simpa [sineFactor] using h0
    simpa [hsin] using (sin_sq_add_cos_sq ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ))))
  have hd : (deriv (sineFactor a) n)^2=4*(kappa:ℂ)^2 := by
    rw [sineFactor_deriv]
    calc
      _ = 4*(kappa:ℂ)^2*cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2 := by ring
      _ = _ := by rw [hc,mul_one]
  obtain ⟨hp2,hp3⟩ := square_zero_product_jets (sineFactor a) g hf hg n h0 h2
  have hp : (fun s => sineFactor a s^2*g s)=P := (funext (P_factor a)).symm
  rw [hp,←waveDerivative_eq_iterated,hd] at hp2 hp3
  have hfc : deriv (finiteC a) n=4*(kappa:ℂ)^2*deriv g n :=
    ((hg n).hasDerivAt.const_mul (4*(kappa:ℂ)^2)).deriv
  constructor
  · have hr := congrArg Complex.re hp2
    change (4*(kappa:ℂ)^2*g n).re= Q n
    unfold Q
    rw [hp2]
    norm_num [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im]
    ring
  · rw [hfc,hp3]
    norm_num [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im]
    ring

lemma kappa_ne_zero : (kappa:ℂ)≠0 := by
  unfold kappa
  exact_mod_cast div_ne_zero Real.pi_ne_zero (by norm_num : (36:ℝ)≠0)
lemma residue_bounds (a : Fin 15) : 0≤residue a ∧ residue a<36 := by
  fin_cases a <;> norm_num [residue]
lemma sineFactor_ne_zero {a : Fin 15} {n : ℤ} (hn : n%36≠residue a) :
    sineFactor a n≠0 := by
  intro hz
  have hsin : sin ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))=0 := by simpa [sineFactor] using hz
  obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hsin
  have hprod : ((n:ℂ)-(residue a:ℂ)-36*(k:ℂ))*(Real.pi:ℂ)=0 := by
    unfold kappa at hk
    push_cast at hk
    linear_combination 36*hk
  have hzero := (mul_eq_zero.mp hprod).resolve_right (by exact_mod_cast Real.pi_ne_zero)
  have hnint : n-residue a-36*k=0 := by exact_mod_cast hzero
  obtain ⟨hr0,hr36⟩ := residue_bounds a
  have hh := Int.emod_add_mul_ediv n 36
  omega

lemma finiteC_P (a : Fin 15) :
    (fun s => (sineFactor a s)^2*finiteC a s) = fun s => 4*(kappa:ℂ)^2*P s := by
  funext s
  rw [P_factor a]
  unfold finiteC
  ring
lemma finiteC_other_jets (a : Fin 15) (n : Node) (hn : n.val%36≠residue a) :
    finiteC a n.val=0 ∧ deriv (finiteC a) n.val=0 := by
  have hne : (sineFactor a n.val)^2≠0 := pow_ne_zero 2 (sineFactor_ne_zero hn)
  have hh := congrFun (finiteC_P a) (n.val:ℂ)
  have hc : finiteC a n.val=0 := by
    apply (mul_eq_zero.mp (show (sineFactor a n.val)^2*finiteC a n.val=0 by
      simpa [P_node] using hh)).resolve_left hne
  refine ⟨hc,?_⟩
  have hf : Differentiable ℂ (sineFactor a) := by unfold sineFactor; fun_prop
  have hd := (((hf (n.val:ℂ)).hasDerivAt.pow 2).mul
    ((differentiable_finiteC a (n.val:ℂ)).hasDerivAt)).deriv
  change deriv (fun s => (sineFactor a s)^2*finiteC a s) n.val = _ at hd
  rw [finiteC_P] at hd
  have hr := ((differentiable_P (n.val:ℂ)).hasDerivAt.const_mul (4*(kappa:ℂ)^2)).deriv
  rw [deriv_P_node,mul_zero] at hr
  rw [hr,hc,mul_zero,zero_add] at hd
  apply (mul_eq_zero.mp (show (sineFactor a n.val)^2*deriv (finiteC a) n.val=0 by simpa using hd.symm)).resolve_left hne

def finiteRatio (a : Fin 15) (s : ℂ) : ℂ :=
  sin ((kappa:ℂ)*(s-(residue a:ℂ)))*cos ((kappa:ℂ)*(s-(residue a:ℂ)))/(kappa:ℂ)
lemma finiteD_eq_ratio (a : Fin 15) : finiteD a =fun s => finiteRatio a s*finiteC a s := by
  funext s
  unfold finiteD finiteRatio finiteC sineFactor
  field_simp [kappa_ne_zero]
  ring
lemma differentiable_finiteRatio (a : Fin 15) : Differentiable ℂ (finiteRatio a) := by
  unfold finiteRatio
  fun_prop
lemma finiteRatio_matching (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    finiteRatio a n=0 ∧ deriv (finiteRatio a) n=1 := by
  have hz := sineFactor_at_residue a n hn
  have hsin : sin ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))=0 := by simpa [sineFactor] using hz
  have hc : cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2=1 := by
    simpa [hsin] using sin_sq_add_cos_sq ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))
  constructor
  · simp [finiteRatio,hsin]
  · have hθ := ((hasDerivAt_id (n:ℂ)).sub_const (residue a:ℂ)).const_mul (kappa:ℂ)
    have hh := ((hθ.csin.mul hθ.ccos).div_const (kappa:ℂ)).deriv
    change deriv (finiteRatio a) n = _ at hh
    rw [hh]
    simp only [id_eq,mul_one,hsin,zero_mul,add_zero]
    calc
      _ = ((kappa:ℂ)*cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2)/(kappa:ℂ) := by ring
      _ = _ := by rw [mul_div_cancel_left₀ _ kappa_ne_zero,hc]
lemma finiteD_matching_jets (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    finiteD a n=0 ∧ deriv (finiteD a) n=finiteC a n := by
  obtain ⟨h0,h1⟩ := finiteRatio_matching a n hn
  constructor
  · rw [finiteD_eq_ratio]
    simp only [h0,zero_mul]
  · have hh := (((differentiable_finiteRatio a (n:ℂ)).hasDerivAt).mul
      ((differentiable_finiteC a (n:ℂ)).hasDerivAt)).deriv
    change deriv (fun s => finiteRatio a s*finiteC a s) _ = _ at hh
    rw [←finiteD_eq_ratio,h0,h1,zero_mul,one_mul,add_zero] at hh
    exact hh
lemma finiteD_other_jets (a : Fin 15) (n : Node) (hn : n.val%36≠residue a) :
    finiteD a n.val=0 ∧ deriv (finiteD a) n.val=0 := by
  obtain ⟨h0,h1⟩ := finiteC_other_jets a n hn
  constructor
  · rw [finiteD_eq_ratio]
    simp only [h0,mul_zero]
  · have hh := (((differentiable_finiteRatio a (n.val:ℂ)).hasDerivAt).mul
      ((differentiable_finiteC a (n.val:ℂ)).hasDerivAt)).deriv
    change deriv (fun s => finiteRatio a s*finiteC a s) _ = _ at hh
    rw [←finiteD_eq_ratio,h0,h1,mul_zero,mul_zero,add_zero] at hh
    exact hh
end AtomicTriangular.Construction
end

end OAI
