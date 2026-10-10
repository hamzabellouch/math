import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.RealRootCoordinates
import OAI.Combinatorics.Chromatic.GradedAlgebra.RootMutationInventory

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus
open Classical
noncomputable section
variable {n : ℕ} {M : Type*} [AddCommGroup M]

def levelGaps (d : Fin (n+1) → M) (w : Cell n → M) (q : List (Cell n)) (i : Fin n) : List M :=
  ForwardChain.gaps (d i.castSucc) ((levelQueue q i).map w) (d i.succ)
def forwardInventory (d : Fin (n+1) → M) (w : Cell n → M) (q : List (Cell n)) : List M :=
  (List.finRange n).flatMap (levelGaps d w q)

lemma forwardInventory_level_nodup (d : Fin (n+1) → M) (w : Cell n → M) (q : List (Cell n))
    (hnd : (forwardInventory d w q).Nodup) (i : Fin n) : (levelGaps d w q i).Nodup :=
  (List.nodup_flatMap.mp hnd).1 i (List.mem_finRange i)

lemma levelGaps_root_mem (d : Fin (n+1) → M) (w : Cell n → M) (b : Cell n) (q : List (Cell n)) :
    w b-d b.1.castSucc ∈ levelGaps d w (b::q) b.1 := by
  simp [levelGaps,levelQueue_cons,ForwardChain.gaps]

lemma forwardInventory_root_mem (d : Fin (n+1) → M) (w : Cell n → M) (b : Cell n) (q : List (Cell n)) :
    w b-d b.1.castSucc ∈ forwardInventory d w (b::q) := by
  exact List.mem_flatMap.mpr ⟨b.1,List.mem_finRange _,levelGaps_root_mem d w b q⟩

private lemma pairwise_distinct {A : Type*} {R : A → A → Prop} (hs:Std.Symm R)
    {l:List A} (h:l.Pairwise R) {a b:A} (ha:a∈l) (hb:b∈l) (hab:a≠b) : R a b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hhead,htail⟩:=List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with hax|hax
    · subst a
      rcases List.mem_cons.mp hb with hbx|hbx
      · exact (hab hbx.symm).elim
      · exact hhead b hbx
    · rcases List.mem_cons.mp hb with hbx|hbx
      · subst b; exact hs.symm _ _ (hhead a hax)
      · exact ih htail hax hbx

variable (Ω : M →+ M →+ ℤ)
lemma forwardInventory_rotation (d : Fin (n+1) → M) (w : Cell n → M) (b : Cell n) (q : List (Cell n))
    (hb : b∉q) (hnd : (forwardInventory d w (b::q)).Nodup)
    (p : M) (hp : p=w b-d b.1.castSucc)
    (hd : ∀j, Ω p (d j)=(if j=b.1.castSucc then 1 else 0)-(if j=b.1.succ then 1 else 0))
    (hw : ∀c,Ω p (w c)=if c=b then 1 else 0) :
    ((forwardInventory d w (b::q)).map (rootMutation Ω p)).Perm
      (forwardInventory d (Function.update w b (d b.1.succ+p)) (q++[b])) := by
  have hwb:Ω p (w b)=1:=by rw [hw,ite_eq_left rfl]
  have hda:Ω p (d b.1.castSucc)=1:=by rw [hd]; simp [Fin.ext_iff]
  have hdc:Ω p (d b.1.succ)= -1:=by rw [hd]; simp [Fin.ext_iff]
  have ho (i:Fin n) : ((levelQueue q i).map (Function.update w b (d b.1.succ+p)))=
      (levelQueue q i).map w := by
    apply queue_update_off
    intro hh
    exact hb (List.mem_of_mem_filter hh)
  have hlevel (i:Fin n) : ((levelGaps d w (b::q) i).map (rootMutation Ω p)).Perm
      (levelGaps d (Function.update w b (d b.1.succ+p)) (q++[b]) i) := by
    by_cases hi:b.1=i
    · subst i
      have hni:=forwardInventory_level_nodup d w (b::q) hnd b.1
      simp only [levelGaps,levelQueue_cons,ite_true,List.map_cons] at hni ⊢
      rw [levelQueue_rotate,ite_eq_left rfl,List.map_append,ho]
      simp only [List.map_cons,List.map_nil,Function.update_self]
      apply rootMutation_rotation_perm Ω p (d b.1.castSucc) (w b) (d b.1.succ) _ hp hda hwb hdc _ hni
      intro x hx
      obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hx
      have hcb:c≠b:=by intro h; subst c; exact hb (List.mem_of_mem_filter hc)
      rw [hw,ite_eq_right hcb]
    · have hnot:p∉levelGaps d w (b::q) i := by
        have H:=(List.nodup_flatMap.mp hnd).2
        have hbi:b.1∈List.finRange n:=List.mem_finRange _
        have hii:i∈List.finRange n:=List.mem_finRange _
        have hpp:p∈levelGaps d w (b::q) b.1:=by rw [hp]; exact levelGaps_root_mem d w b q
        have hdis:List.Disjoint (levelGaps d w (b::q) b.1) (levelGaps d w (b::q) i):=by
          exact pairwise_distinct ⟨fun _ _ hdisjoint=>hdisjoint.symm⟩ H hbi hii hi
        exact fun hpi=>hdis hpp hpi
      have ha:Ω p (d i.castSucc)≤0:=by
        rw [hd]
        have hn:i.castSucc≠b.1.castSucc:=fun h=>hi (Fin.castSucc_inj.mp h).symm
        simp only [ite_eq_right hn]
        split_ifs <;> norm_num
      have hc:0≤Ω p (d i.succ):=by
        rw [hd]
        have hn:i.succ≠b.1.succ:=fun h=>hi (Fin.succ_inj.mp h).symm
        simp only [ite_eq_right hn,sub_zero]
        split_ifs <;> norm_num
      simp only [levelGaps,levelQueue_cons,ite_eq_right hi] at hnot ⊢
      rw [levelQueue_rotate,ite_eq_right hi,List.append_nil,ho]
      apply List.Perm.of_eq
      apply rootMutation_gaps_fixed Ω p _ _ _ ha hc _ hnot
      intro x hx
      obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hx
      have hcb:c≠b:=by intro h; subst c; exact hb (List.mem_of_mem_filter hc)
      rw [hw,ite_eq_right hcb]
  rw [forwardInventory,List.map_flatMap]
  exact (List.Perm.refl _).flatMap (fun i _=>hlevel i)
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.QuantumTorus
open Classical
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]

private def pivotMap (pc:I) (a:I → ℝ) : (I → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun d i:=if i=pc then -d pc+∑j∈Finset.univ.erase pc,a j*d j else d i
  map_add' x y:=by
    ext i
    by_cases hi:i=pc
    · subst i; simp only [ite_true,Pi.add_apply,neg_add,mul_add,Finset.sum_add_distrib]; ring
    · simp [hi]
  map_smul' r x:=by
    ext i
    by_cases hi:i=pc
    · subst i
      simp only [ite_true,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_add,mul_neg,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simp [hi]

private lemma pivot_involutive (pc:I) (a:I → ℝ) : Function.Involutive (pivotMap pc a) := by
  intro d
  ext i
  by_cases hi:i=pc
  · subst i
    simp only [pivotMap,LinearMap.coe_mk,AddHom.coe_mk,ite_true]
    have hh:(∑j∈Finset.univ.erase pc,a j*(if j=pc then -d pc+∑k∈Finset.univ.erase pc,a k*d k else d j))=
        ∑j∈Finset.univ.erase pc,a j*d j:=by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_right (Finset.mem_erase.mp hj).1]
    rw [hh]; ring
  · simp [pivotMap,hi]

private lemma pivot_single (pc i:I) (a:I → ℝ) :
    pivotMap pc a (Pi.single i 1)=if i=pc then -Pi.single pc 1 else Pi.single i 1+a i • Pi.single pc 1 := by
  ext j
  by_cases hip:i=pc
  · subst i
    simp only [pivotMap,LinearMap.coe_mk,AddHom.coe_mk,ite_true]
    have hs:(∑k∈Finset.univ.erase pc,a k*(Pi.single pc 1:I → ℝ) k)=0:=by
      apply Finset.sum_eq_zero
      intro k hk
      simp [Ne.symm (Finset.mem_erase.mp hk).1]
    rw [hs]
    by_cases hj:j=pc
    · subst j; simp
    · simp [hj]
  · simp only [pivotMap,LinearMap.coe_mk,AddHom.coe_mk,ite_eq_right hip]
    have hs:(∑k∈Finset.univ.erase pc,a k*(Pi.single i 1:I → ℝ) k)=a i:=by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · simp [hip]
    rw [hs]
    by_cases hj:j=pc
    · subst j; simp [Ne.symm hip]
    · simp [hj,Pi.single_apply]

variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)
lemma mutatedRoots_realIndependent (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) :
    LinearIndependent ℝ (fun i=>e (simpleRoot (mutatedRoots Ω C pc) i)) := by
  obtain ⟨D,hD⟩:=realRootCoordinates_exists C e hC
  let a:I → ℝ:=fun i=>(max 0 (-mutationPairing Ω C pc i):ℤ)
  have hmap (i:I) : D (e (simpleRoot (mutatedRoots Ω C pc) i))=
      pivotMap pc a (Pi.single i 1) := by
    rw [pivot_single]
    by_cases hi:i=pc
    · subst i
      rw [ite_eq_left rfl,mutatedRoot_p,map_neg,map_neg,real_coordinate_simple C e D hD]
    · rw [ite_eq_right hi,mutatedRoot_off Ω C pc i hi,map_add,map_zsmul,map_add,map_zsmul,
        real_coordinate_simple C e D hD,real_coordinate_simple C e D hD]
      simp only [a,Int.cast_smul_eq_zsmul]
  have hind:LinearIndependent ℝ (fun i=>pivotMap pc a (Pi.single i 1)):=
    (Pi.linearIndependent_single_one I ℝ).map' (pivotMap pc a)
      (LinearMap.ker_eq_bot.mpr (pivot_involutive pc a).injective)
  have hd:LinearIndependent ℝ (fun i=>D (e (simpleRoot (mutatedRoots Ω C pc) i))):=by
    simpa only [hmap] using hind
  exact hd.of_comp D

lemma rootDegreeCovector_exists (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) :
    ∃L:Module.Dual ℝ E,∀n m,HasRootDegree C n m → L (e m)=(n:ℝ) := by
  obtain ⟨D,hD⟩:=realRootCoordinates_exists C e hC
  let L:Module.Dual ℝ E:=∑i,(LinearMap.proj i).comp D
  refine ⟨L,fun n m hm=>covector_root_eval C e L ?_ hm⟩
  intro i
  simp only [L,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    real_coordinate_simple C e D hD]
  simp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
