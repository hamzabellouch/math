import Mathlib
import OAI.Probability.LogConcave.JetEstimates.AllSplitBound

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Function
open scoped Classical BigOperators

def zeroExtend {I J : Type*} (e : I ↪ J) (f : I → ℝ) : J → ℝ :=
  Function.extend e f (fun _ => 0)

@[simp] lemma zeroExtend_apply {I J : Type*} (e : I ↪ J) (f : I → ℝ) (i : I) :
    zeroExtend e f (e i)=f i := e.injective.extend_apply f _ i
lemma zeroExtend_out {I J : Type*} (e : I ↪ J) (f : I → ℝ) {j : J} (hj : j∉Set.range e) :
    zeroExtend e f j=0 := Function.extend_apply' _ _ _ hj

lemma zeroExtend_sum {I J : Type*} [Fintype I] [Fintype J] (e : I ↪ J) (f : I → ℝ) :
    (∑j,zeroExtend e f j)=∑i,f i :=
  (Fintype.sum_of_injective e e.injective f (zeroExtend e f)
    (fun _ hj => zeroExtend_out e f hj) (fun i => (zeroExtend_apply e f i).symm)).symm

lemma zeroExtend_sq {I J : Type*} (e : I ↪ J) (f : I → ℝ) :
    (fun j => (zeroExtend e f j)^2)=zeroExtend e (fun i => (f i)^2) := by
  funext j
  by_cases hj : j∈Set.range e
  · obtain ⟨i,rfl⟩ := hj; simp
  · rw [zeroExtend_out e f hj,zeroExtend_out e _ hj]; norm_num

lemma zeroExtend_mul {I J : Type*} (e : I ↪ J) (f : I → ℝ) (g : J → ℝ) :
    (fun j => zeroExtend e f j*g j)=zeroExtend e (fun i => f i*g (e i)) := by
  funext j
  by_cases hj : j∈Set.range e
  · obtain ⟨i,rfl⟩ := hj; simp
  · rw [zeroExtend_out e f hj,zeroExtend_out e _ hj]; simp

lemma sum_restrict_le {I J : Type*} [Fintype I] [Fintype J] (e : I ↪ J) (f : J → ℝ)
    (hf : ∀j,0≤f j) : (∑i,f (e i))≤∑j,f j := by
  rw [←Finset.sum_image (f:=f) (g:=(e : I → J)) (by intro i _ j _ h; exact e.injective h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hf j)

lemma Bound.zeroExtend {I O I' O' : Type*} [Fintype I] [Fintype O] [Fintype I'] [Fintype O']
    {A : O → I → ℝ} {C : ℝ} (hA : Bound A C) (hC : 0≤C)
    (eI : I ↪ I') (eO : O ↪ O') :
    Bound (fun o i => TensorEnergy.zeroExtend eO (fun o => TensorEnergy.zeroExtend eI (A o) i) o) C := by
  intro v
  have he : (fun o => ∑i,TensorEnergy.zeroExtend eO (fun o => TensorEnergy.zeroExtend eI (A o) i) o*v i)=
      TensorEnergy.zeroExtend eO (fun o => ∑i,A o i*v (eI i)) := by
    funext o
    by_cases ho : o∈Set.range eO
    · obtain ⟨o,rfl⟩ := ho
      simp only [zeroExtend_apply]
      rw [zeroExtend_mul,zeroExtend_sum]
    · simp only [zeroExtend_out eO _ ho,zero_mul,Finset.sum_const_zero]
  change (∑o,((fun o => ∑i,TensorEnergy.zeroExtend eO (fun o => TensorEnergy.zeroExtend eI (A o) i) o*v i) o)^2)≤_
  rw [he,zeroExtend_sq,zeroExtend_sum]
  exact (hA (fun i => v (eI i))).trans
    (mul_le_mul_of_nonneg_left (sum_restrict_le eI (fun i => (v i)^2) (fun _ => sq_nonneg _)) hC)

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Function
open scoped Classical BigOperators

def slotEmbedding {S : Type*} {d D : ℕ} (e : S → Fin d ↪ Fin D) :
    (S → Fin d) ↪ (S → Fin D) where
  toFun c s := e s (c s)
  inj' := by intro a b h; funext s; exact (e s).injective (congrFun h s)

@[simp] lemma slotEmbedding_apply {S : Type*} {d D : ℕ} (e : S → Fin d ↪ Fin D)
    (c : S → Fin d) (s : S) : slotEmbedding e c s=e s (c s) := rfl

lemma AllSplitBound.zeroExtend {S : Type} [Fintype S] {d D : ℕ}
    {T : (S → Fin d) → ℝ} {M : ℝ} (hT : AllSplitBound T M) (ι : S → Fin d ↪ Fin D) :
    AllSplitBound (TensorEnergy.zeroExtend (slotEmbedding ι) T) M := by
  intro I O _ _ _ _ _ _ e
  let ei := slotEmbedding (fun i => ι (e.symm (.inl i)))
  let eo := slotEmbedding (fun o => ι (e.symm (.inr o)))
  have he (i : I → Fin d) (o : O → Fin d) :
      (fun s => Sum.elim (ei i) (eo o) (e s))=
      slotEmbedding ι (fun s => Sum.elim i o (e s)) := by
    funext s
    rcases h : e s with a|b <;>
      simp only [h,Sum.elim_inl,Sum.elim_inr,ei,eo,slotEmbedding_apply,e.symm_apply_eq.mpr h.symm]
  have hrow (o : O → Fin D) (i : I → Fin D) :
      TensorEnergy.zeroExtend (slotEmbedding ι) T (fun s => Sum.elim i o (e s))=
      TensorEnergy.zeroExtend eo (fun o => TensorEnergy.zeroExtend ei (fun i => T (fun s => Sum.elim i o (e s))) i) o := by
    by_cases hi : i∈Set.range ei
    · obtain ⟨a,rfl⟩ := hi
      by_cases ho : o∈Set.range eo
      · obtain ⟨b,rfl⟩ := ho
        rw [he,zeroExtend_apply,zeroExtend_apply,zeroExtend_apply]
      · rw [zeroExtend_out eo _ ho,zeroExtend_out]
        rintro ⟨c,hc⟩
        apply ho
        refine ⟨fun b => c (e.symm (.inr b)),?_⟩
        funext b
        have hh := congrFun hc (e.symm (.inr b))
        change ι (e.symm (.inr b)) (c (e.symm (.inr b)))=o b
        simpa only [slotEmbedding_apply,Equiv.apply_symm_apply,Sum.elim_inr] using hh
    · rw [zeroExtend_out]
      · by_cases ho : o∈Set.range eo
        · obtain ⟨b,rfl⟩ := ho
          rw [zeroExtend_apply,zeroExtend_out ei _ hi]
        · rw [zeroExtend_out eo _ ho]
      · rintro ⟨c,hc⟩
        apply hi
        refine ⟨fun a => c (e.symm (.inl a)),?_⟩
        funext a
        have hh := congrFun hc (e.symm (.inl a))
        change ι (e.symm (.inl a)) (c (e.symm (.inl a)))=i a
        simpa only [slotEmbedding_apply,Equiv.apply_symm_apply,Sum.elim_inl] using hh
  have hb := (hT I O e).zeroExtend (sq_nonneg M) ei eo
  convert hb using 1
  ext o i
  exact hrow o i
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
