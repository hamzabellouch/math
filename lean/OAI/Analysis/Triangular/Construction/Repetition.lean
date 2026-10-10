import OAI.Analysis.Triangular.Envelope.KernelBounds

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
lemma pi_eta_pos : 0<Real.pi*eta := mul_pos Real.pi_pos (by norm_num [eta])
def repetitionRatio : ℝ := Real.exp (-36*Real.pi*eta)
def repetitionNorm : ℝ := (1+Real.pi*eta)*repetitionRatio/(1-repetitionRatio)
lemma repetitionRatio_pos : 0<repetitionRatio := Real.exp_pos _
lemma repetitionRatio_lt : repetitionRatio<1 := by
  rw [repetitionRatio,Real.exp_lt_one_iff]
  nlinarith [pi_eta_pos]
lemma repetitionNorm_eq : repetitionNorm = (1+Real.pi*eta)/(Real.exp (36*Real.pi*eta)-1) := by
  have he0 : Real.exp (36*Real.pi*eta)≠0 := (Real.exp_pos _).ne'
  have he1 : Real.exp (36*Real.pi*eta)≠1 := ne_of_gt (Real.one_lt_exp_iff.mpr (by nlinarith [pi_eta_pos]))
  unfold repetitionNorm repetitionRatio
  rw [show -36*Real.pi*eta = -(36*Real.pi*eta) by ring,Real.exp_neg]
  field_simp

def repetitionEnvelope (a : Fin 11) (n : TailNode) : ℝ :=
  if n.val.val%36=residue ⟨a.val,by omega⟩ then
    (1+Real.pi*eta)*Real.exp (-Real.pi*eta*n.val.val) else 0
lemma repetitionEnvelope_nonneg (a : Fin 11) (n : TailNode) : 0≤repetitionEnvelope a n := by
  unfold repetitionEnvelope
  split_ifs
  · exact mul_nonneg (by linarith [pi_eta_pos]) (Real.exp_pos _).le
  · rfl
lemma repetitionEnvelope_enumerate (a : Fin 11) (r : Fin 15) (l : ℕ) :
    repetitionEnvelope a (enumerateTail (r,l)) =
      if r=⟨a.val,by omega⟩ then
        (1+Real.pi*eta)*Real.exp (-Real.pi*eta*tailBase r)*repetitionRatio^l else 0 := by
  have hm : (enumerateTail (r,l)).val.val%36=residue r := by
    change (tailBase r+36*(l:ℤ))%36=residue r
    simp [Int.add_emod,tailBase_mod,residue_mod]
  unfold repetitionEnvelope
  simp only [hm,residue_injective.eq_iff]
  split_ifs
  · change _ * Real.exp (-Real.pi*eta*((tailBase r+36*(l:ℤ):ℤ):ℝ)) = _
    rw [show -Real.pi*eta*((tailBase r+36*(l:ℤ):ℤ):ℝ) =
      -Real.pi*eta*(tailBase r:ℝ)+(l:ℝ)*(-36*Real.pi*eta) by push_cast; ring,
      Real.exp_add,Real.exp_nat_mul]
    simp only [repetitionRatio]; ring
  · rfl
lemma summable_repetitionEnvelope (a : Fin 11) : Summable (repetitionEnvelope a) := by
  apply tailEnumeration.summable_iff.mp
  apply (summable_prod_of_nonneg (fun p => repetitionEnvelope_nonneg a _)).mpr
  refine ⟨fun r => ?_,(hasSum_fintype _).summable⟩
  change Summable (fun l : ℕ => repetitionEnvelope a (enumerateTail (r,l)))
  simp_rw [repetitionEnvelope_enumerate]
  split_ifs
  · exact (summable_geometric_of_lt_one repetitionRatio_pos.le repetitionRatio_lt).mul_left _
  · exact summable_zero
lemma tsum_repetitionEnvelope (a : Fin 11) :
    (∑' n, repetitionEnvelope a n) =
      (1+Real.pi*eta)*Real.exp (-Real.pi*eta*tailBase ⟨a.val,by omega⟩)/(1-repetitionRatio) := by
  rw [← tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr (summable_repetitionEnvelope a)
  change Summable (fun p : Fin 15 × ℕ => repetitionEnvelope a (enumerateTail p)) at hs
  change (∑' p : Fin 15 × ℕ, repetitionEnvelope a (enumerateTail p)) = _
  rw [hs.tsum_prod,tsum_fintype]
  simp_rw [repetitionEnvelope_enumerate]
  have hi (P : Prop) [Decidable P] (f : ℕ → ℝ) :
      (∑' l, if P then f l else 0) = if P then ∑' l, f l else 0 := by
    by_cases hh : P <;> simp [hh]
  simp_rw [hi]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,tsum_mul_left,
    tsum_geometric_of_lt_one repetitionRatio_pos.le repetitionRatio_lt,div_eq_mul_inv]
lemma repetitionEnvelope_bound (a : Fin 11) : (∑' n, repetitionEnvelope a n) ≤ repetitionNorm := by
  rw [tsum_repetitionEnvelope]
  have ht : 36 ≤ tailBase ⟨a.val,by omega⟩ := by revert a; decide +kernel
  have he : Real.exp (-Real.pi*eta*(tailBase ⟨a.val,by omega⟩:ℝ)) ≤ repetitionRatio := by
    unfold repetitionRatio
    apply Real.exp_le_exp.mpr
    have ht' : (36:ℝ) ≤ (tailBase ⟨a.val,by omega⟩:ℝ) := by exact_mod_cast ht
    nlinarith [pi_eta_pos]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr repetitionRatio_lt).le
  exact mul_le_mul_of_nonneg_left he (by linarith [pi_eta_pos])

def repetitionEntry (c d : Fin 2) : ℝ :=
  if c.val=0 then if d.val=0 then 1 else -Real.pi*eta
  else if d.val=0 then 0 else 1
lemma repetitionEntry_bound (c : Fin 2) : (∑ d : Fin 2, |repetitionEntry c d|) ≤ 1+Real.pi*eta := by
  fin_cases c <;> norm_num [Fin.sum_univ_succ,repetitionEntry,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num [eta] : 0<eta)]
  exact pi_eta_pos.le
def repetitionKernel (p : TailNode × Fin 2) (a : Fin 11) (c : Fin 2) : ℝ :=
  if p.1.val.val%36=residue ⟨a.val,by omega⟩ then
    Real.exp (-Real.pi*eta*p.1.val.val)*repetitionEntry c p.2 else 0
lemma repetitionKernel_pair (a : Fin 11) (c : Fin 2) (n : TailNode) :
    (∑ d : Fin 2, |repetitionKernel (n,d) a c|) ≤ repetitionEnvelope a n := by
  unfold repetitionKernel repetitionEnvelope
  split_ifs with hh
  · simp only [abs_mul,abs_of_pos (Real.exp_pos _),←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (repetitionEntry_bound c) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · simp
lemma repetitionKernel_bounds (a : Fin 11) (c : Fin 2) :
    Summable (fun p => |repetitionKernel p a c|) ∧
      (∑' p, |repetitionKernel p a c|) ≤ repetitionNorm := by
  obtain ⟨hs,hb⟩ := paired_summable_bound (fun n d => repetitionKernel (n,d) a c)
    (repetitionEnvelope a) (summable_repetitionEnvelope a) (repetitionKernel_pair a c)
  exact ⟨hs,hb.trans (repetitionEnvelope_bound a)⟩
end AtomicTriangular.Construction
end

end OAI
