import OAI.Dynamics.StandardMap.GridWordIntegrals

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma blockAtom_measurable {r:ℕ} (f:Torus → Torus) (hf:Measurable f) (p:FinitePartition r)
    (n:ℕ) (w:Fin n → Fin (r+1)) : MeasurableSet (blockAtom f p n w) := by
  have h:=MeasurableSet.iInter (fun i:Fin n=>(p.property.comp (hf.iterate i.val)) (measurableSet_singleton (w i)))
  convert h using 1
  ext z
  simp only [blockAtom,mem_ofPred_eq,mem_iInter,mem_preimage,mem_singleton_iff,Function.comp_apply]
lemma blockAtom_iUnion {r:ℕ} (f:Torus → Torus) (p:FinitePartition r) (n:ℕ) :
    (⋃w:Fin n → Fin (r+1),blockAtom f p n w)=univ := by
  apply eq_univ_of_forall
  intro z
  exact mem_iUnion.mpr ⟨fun i=>p.val (f^[i.val] z),fun _=>rfl⟩
lemma blockAtom_disjoint {r:ℕ} (f:Torus → Torus) (p:FinitePartition r) (n:ℕ) :
    Pairwise (Function.onFun Disjoint (blockAtom f p n)) := by
  intro w v hne
  apply Set.disjoint_left.mpr
  intro z hz hv
  apply hne
  funext i
  exact (hz i).symm.trans (hv i)
lemma sum_block_integral {r:ℕ} (μ:Measure Torus) (f:Torus → Torus) (hf:Measurable f)
    (p:FinitePartition r) (n:ℕ) (g:Torus → ℝ) (hg:Integrable g μ) :
    (∑w:Fin n → Fin (r+1),∫z in blockAtom f p n w,g z ∂μ)=∫z,g z ∂μ := by
  have h:=integral_iUnion (blockAtom_measurable f hf p n) (blockAtom_disjoint f p n) hg.integrableOn
  rw [blockAtom_iUnion,Measure.restrict_univ,tsum_fintype] at h
  exact h.symm
lemma sum_block_mass {r:ℕ} (μ:Measure Torus) [IsProbabilityMeasure μ]
    (f:Torus → Torus) (hf:Measurable f) (p:FinitePartition r) (n:ℕ) :
    (∑w:Fin n → Fin (r+1),(μ (blockAtom f p n w)).toReal)=1 := by
  have h:=sum_block_integral μ f hf p n (fun _=>1) (integrable_const (1:ℝ))
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,measure_univ,ENNReal.toReal_one,smul_eq_mul,mul_one] using h
lemma atom_log_integral_bound (μ:Measure Torus) [IsFiniteMeasure μ] (A:Set Torus)
    (g:Torus → ℝ) (hg:Integrable g μ) (hlog:Integrable (fun z=>Real.log (g z)) μ)
    (hpos:∀z,0<g z) (B:ℝ) (hB:0<B) (hbound:(∫z in A,g z ∂μ)≤B) :
    (∫z in A,Real.log (g z) ∂μ)≤
      (μ A).toReal*Real.log B-(μ A).toReal*Real.log (μ A).toReal := by
  let p:ℝ:=(μ A).toReal
  by_cases he:p=0
  · have hzero:μ A=0 := ((ENNReal.toReal_eq_zero_iff (μ A)).mp he).resolve_right (measure_ne_top μ A)
    rw [Measure.restrict_eq_zero.mpr hzero,integral_zero_measure]
    simp only [← show p=(μ A).toReal from rfl,he,zero_mul,sub_self,le_refl]
  have hp:0<p := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm he)
  let a:ℝ:=B/p
  have ha:0<a := div_pos hB hp
  have hpoint:∀z,Real.log (g z)≤Real.log a+g z/a-1 := by
    intro z
    have h:=Real.log_le_sub_one_of_pos (div_pos (hpos z) ha)
    rw [Real.log_div (hpos z).ne' ha.ne'] at h
    linarith
  have hgA : Integrable g (μ.restrict A) := hg.integrableOn
  have hlA : Integrable (fun z=>Real.log (g z)) (μ.restrict A) := hlog.integrableOn
  have hcA : Integrable (fun _ : Torus => Real.log a) (μ.restrict A) := integrable_const _
  have h1A : Integrable (fun _ : Torus => (1:ℝ)) (μ.restrict A) := integrable_const _
  have hi:=integral_mono hlA ((hcA.add (hgA.div_const a)).sub h1A) hpoint
  simp only [Pi.add_apply,Pi.sub_apply] at hi
  rw [integral_sub (f:=fun z=>Real.log a+g z/a) (g:=fun _=>1) (hcA.add (hgA.div_const a)) h1A,
    integral_add (f:=fun _=>Real.log a) (g:=fun z=>g z/a) hcA (hgA.div_const a),integral_div,
    setIntegral_const,setIntegral_const] at hi
  simp only [smul_eq_mul,mul_one] at hi
  change (∫z in A,Real.log (g z) ∂μ)≤p*Real.log B-p*Real.log p
  have hdiv:(∫z in A,g z ∂μ)/a≤p := by
    apply (div_le_iff₀ ha).mpr
    calc
      _ ≤ B := hbound
      _ = p*a := by dsimp [a]; field_simp
  have hloga:Real.log a=Real.log B-Real.log p := Real.log_div hB.ne' hp.ne'
  change (∫z in A,Real.log (g z) ∂μ)≤p*Real.log a+(∫z in A,g z ∂μ)/a-p at hi
  rw [hloga] at hi
  nlinarith
lemma entropy_from_atom_integrals {r:ℕ} (μ:Measure Torus) [IsProbabilityMeasure μ]
    (f:Torus → Torus) (hf:Measurable f) (p:FinitePartition r) (n:ℕ)
    (g:Torus → ℝ) (hg:Integrable g μ) (hlog:Integrable (fun z=>Real.log (g z)) μ)
    (hpos:∀z,0<g z) (B:ℝ) (hB:0<B)
    (hbound:∀w:Fin n → Fin (r+1),(∫z in blockAtom f p n w,g z ∂μ)≤B) :
    (∫z,Real.log (g z) ∂μ)-Real.log B≤blockEntropy μ f p n := by
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun w _=>atom_log_integral_bound μ (blockAtom f p n w)
    g hg hlog hpos B hB (hbound w))
  rw [sum_block_integral μ f hf p n _ hlog,Finset.sum_sub_distrib,← Finset.sum_mul,
    sum_block_mass μ f hf p n,one_mul] at h
  unfold blockEntropy
  linarith
end StandardMapEntropy

end OAI
