import OAI.Analysis.Triangular.Envelope.KernelBounds
import OAI.Analysis.Triangular.Construction.L1Kernel

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate AtomicTriangular.L1Kernel

def gaussianTarget (v z : ℝ) (n : ℤ) (d : Fin 2) : ℝ :=
  Q 1/Q n * Real.exp (Real.pi*(v-h)*n+(1-n)/z) *
    (if d.val=0 then z else -1+(Real.pi*(v-h)-D n)*z)
def targetEnvelope (v : ℝ) (n : ℤ) : ℝ :=
  Q 1/Q n * (1+Z+Z*|Real.pi*(v-h)-D n|) *
    Real.exp (Real.pi*(v-h)*n+(1-n)/Z)
lemma Q_one_pos : 0<Q 1 := by linarith [Q_1_bounds.1]
lemma targetEnvelope_nonneg (v : ℝ) (n : Node) : 0≤targetEnvelope v n.val := by
  have hn : 0<Q n.val := by linarith [(Q_node_bounds n.val n.property.2).1]
  have hZ : 0<Z := by norm_num [Z]
  unfold targetEnvelope
  exact mul_nonneg (mul_nonneg (div_nonneg Q_one_pos.le hn.le) (by positivity)) (Real.exp_pos _).le
lemma gaussianTarget_pair_bound {z : ℝ} (hz : 0<z) (hzB : z≤Z) (v : ℝ)
    (n : Node) (hn : 1≤n.val) :
    (∑ d : Fin 2, |gaussianTarget v z n.val d|) ≤ targetEnvelope v n.val := by
  have hQ : 0<Q n.val := by linarith [(Q_node_bounds n.val n.property.2).1]
  have hZ : 0<Z := by norm_num [Z]
  have hn' : 0≤(n.val:ℝ)-1 := by
    have hi : (1:ℝ)≤(n.val:ℝ) := by exact_mod_cast hn
    linarith
  have he : Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/z) ≤
      Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/Z) := by
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_left hn' hz hzB
    have hnz : (1-(n.val:ℝ))/z = -(((n.val:ℝ)-1)/z) := by ring
    have hnZ : (1-(n.val:ℝ))/Z = -(((n.val:ℝ)-1)/Z) := by ring
    rw [hnz,hnZ]
    linarith
  have hb : z+|-1+(Real.pi*(v-h)-D n.val)*z| ≤ 1+Z+Z*|Real.pi*(v-h)-D n.val| := by
    have ha := abs_add_le (-1:ℝ) ((Real.pi*(v-h)-D n.val)*z)
    rw [abs_mul,abs_of_pos hz] at ha
    norm_num at ha
    have hm := mul_le_mul_of_nonneg_left hzB (abs_nonneg (Real.pi*(v-h)-D n.val))
    linarith
  have hp : 0≤Q 1/Q n.val := div_nonneg Q_one_pos.le hQ.le
  simp only [Fin.sum_univ_succ,gaussianTarget,Fin.val_zero,Fin.val_succ,Fin.isValue,
    ↓reduceIte,Nat.one_ne_zero,Nat.reduceAdd,abs_mul,abs_of_nonneg hp,abs_of_pos (Real.exp_pos _),abs_of_pos hz]
  unfold targetEnvelope
  calc
    _ = (Q 1/Q n.val)*(z+|-1+(Real.pi*(v-h)-D n.val)*z|)*
        Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/z) := by ring
    _ ≤ (Q 1/Q n.val)*(1+Z+Z*|Real.pi*(v-h)-D n.val|)*
        Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/Z) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb hp) he (Real.exp_pos _).le
        (by positivity)
lemma targetEnvelope_enumerate (a : Fin 15) (l : ℕ) :
    targetEnvelope h (enumerateTail (a,l)).val.val =
      targetEnvelope h (tailBase a)*(Real.exp (-36/Z))^l := by
  unfold targetEnvelope
  rw [Q_enumerateTail,D_enumerateTail]
  simp only [sub_self,mul_zero,zero_mul,zero_add,zero_sub,abs_neg]
  change _ * Real.exp ((1-((tailBase a+36*(l:ℤ):ℤ):ℝ))/Z) = _
  rw [show (1-((tailBase a+36*(l:ℤ):ℤ):ℝ))/Z =
    (1-(tailBase a:ℝ))/Z+(l:ℝ)*(-36/Z) by push_cast; ring,
    Real.exp_add,Real.exp_nat_mul]
  ring
lemma targetRatio_lt : Real.exp (-36/Z)<1 := by
  rw [Real.exp_lt_one_iff]; norm_num [Z]
lemma summable_targetEnvelope : Summable (fun n : TailNode => targetEnvelope h n.val.val) := by
  apply tailEnumeration.summable_iff.mp
  apply (summable_prod_of_nonneg (fun p => targetEnvelope_nonneg h (enumerateTail p).val)).mpr
  refine ⟨fun a => ?_,(hasSum_fintype _).summable⟩
  change Summable (fun l : ℕ => targetEnvelope h (enumerateTail (a,l)).val.val)
  simp_rw [targetEnvelope_enumerate]
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le targetRatio_lt).mul_left _
def finiteTargetEnvelope : ℝ := ∑ i : Fin 6, targetEnvelope H (finiteNode ⟨i.val+4,by omega⟩)
def tailTargetEnvelope : ℝ := (∑ a : Fin 15, targetEnvelope h (tailBase a))/(1-Real.exp (-36/Z))
lemma tsum_targetEnvelope : (∑' n : TailNode, targetEnvelope h n.val.val)=tailTargetEnvelope := by
  rw [←tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr summable_targetEnvelope
  change Summable (fun p : Fin 15 × ℕ => targetEnvelope h (enumerateTail p).val.val) at hs
  change (∑' p : Fin 15 × ℕ, targetEnvelope h (enumerateTail p).val.val)=_
  rw [hs.tsum_prod]
  simp_rw [targetEnvelope_enumerate,tsum_mul_left,
    tsum_geometric_of_lt_one (Real.exp_pos _).le targetRatio_lt]
  rw [tsum_fintype,←Finset.sum_mul]
  rfl
lemma tailTarget_bounds {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    Summable (fun p : TailNode × Fin 2 => |gaussianTarget h z p.1.val.val p.2|) ∧
      (∑' p : TailNode × Fin 2, |gaussianTarget h z p.1.val.val p.2|) ≤ tailTargetEnvelope := by
  obtain ⟨hs,hb⟩ := paired_summable_bound (fun (n : TailNode) d => gaussianTarget h z n.val.val d)
    (fun n => targetEnvelope h n.val.val) summable_targetEnvelope
    (fun n => gaussianTarget_pair_bound hz hzB h n.val (by have := n.val.property.1; omega))
  exact ⟨hs,hb.trans_eq tsum_targetEnvelope⟩
def tailTarget (z : ℝ) (hz : 0<z) (hzB : z≤Z) : ℓ¹(TailNode × Fin 2,ℝ) :=
  column (fun p (_ : Unit) => gaussianTarget h z p.1.val.val p.2)
    (fun _ => (tailTarget_bounds hz hzB).1) ()
lemma tailTarget_norm {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖tailTarget z hz hzB‖ ≤ tailTargetEnvelope := by
  rw [l1_norm]
  exact (tailTarget_bounds hz hzB).2
end AtomicTriangular.Construction
end

end OAI
