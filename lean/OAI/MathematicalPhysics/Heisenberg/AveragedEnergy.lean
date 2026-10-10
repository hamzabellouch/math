import OAI.MathematicalPhysics.Heisenberg.HoleReturns

namespace OAI

section
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
open Filter
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
attribute [local instance] exposureDecEq
attribute [-instance] exposureDecEq

namespace Heisenberg.Exposure
attribute [local irreducible] killedMean Heisenberg.Hitting.hitting Heisenberg.Hitting.energy Heisenberg.Cycle.MissingSet layerHistory
open Heisenberg.Return Heisenberg.Hitting Heisenberg.Cycle Heisenberg.Conditioning
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem averaged_layer_energy {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (p : Fin n → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1) (P : Set (Fin n×V))
    (D : (Fin n → Bool) → Set (Fin n×V)) (T : Finset P)
    (hT : ∀ base j,j∈T → j.val∈D base)
    (hQ : ∀ base,(MissingSet (layerHistory s (fun i => Equiv.swap (a i) (b i)) base) P)ᶜ∩Pᶜ ⊆ D base) :
    let τ := fun i => Equiv.swap (a i) (b i)
    let μ₀ := productWeight (fun i z => if z then p i else 1-p i)
    let μ := fun c => μ₀ c*(2:ℝ)^missingCount (layerHistory s τ c) P
    let θ := fun c => μ c/(∑ b,μ b)
    let σ := fun base c => layerHistory s τ
      (residualCoins (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c)
    (∑ c,θ c*returnCount (layerHistory s τ c) P T) ≤ (T.card:ℝ)-
      ∑ base,θ base*energy (killedMean μ₀ (σ base) (D base))
        (hitting (killedMean μ₀ (σ base) (D base)) (T.image Subtype.val)) := by
  dsimp only
  let τ := fun i => Equiv.swap (a i) (b i)
  let w : Fin n → Bool → ℝ := fun i z => if z then p i else 1-p i
  let μ := fun c => productWeight w c*(2:ℝ)^missingCount (layerHistory s τ c) P
  let Z := ∑ c,μ c
  let e := fun base => energy
    (killedMean (productWeight w) (fun c => layerHistory s τ
      (residualCoins (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c)) (D base))
    (hitting (killedMean (productWeight w) (fun c => layerHistory s τ
      (residualCoins (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c)) (D base))
      (T.image Subtype.val))
  have hw0 : ∀ i z,0≤w i z := by
    intro i z
    cases z <;> simp only [w,Bool.false_eq_true,↓reduceIte] <;> linarith [(hp i).1,(hp i).2]
  have hμ : ∀ c,0≤μ c := fun c => mul_nonneg (productWeight_nonneg w hw0 c) (by positivity)
  have hZ : 0<Z := by
    have hs : (∑ c : Fin n → Bool,productWeight w c)=1 := by
      convert productWeight_sum w (by intro i; simp [w]) using 1
      congr 1
      ext c
      simp
    apply lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    rw [←hs]
    exact Finset.sum_le_sum (fun c _ => le_mul_of_one_le_right (productWeight_nonneg w hw0 c)
      (one_le_pow₀ (by norm_num)))
  have h : (∑ c,μ c*returnCount (layerHistory s τ c) P T)≤∑ c,μ c*((T.card:ℝ)-e c) := by
    apply expected_le μ hμ (layerExposure s τ P) (layerExposure_equivalence s τ P)
    intro base hb
    simpa only [τ,μ,w,e] using
      (exposed_layer_energy s a b p hp P base (left_ne_zero_of_mul hb) (D base) T (hT base) (hQ base))
  have hh := div_le_div_of_nonneg_right h hZ.le
  have he : (∑ c,μ c*((T.card:ℝ)-e c))/Z = (T.card:ℝ)-(∑ c,μ c*e c)/Z := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
    change (Z*(T.card:ℝ)-(∑ c,μ c*e c))/Z = _
    rw [sub_div,mul_div_cancel_left₀ _ hZ.ne']
  rw [he] at hh
  simpa only [Finset.sum_div,div_mul_eq_mul_div] using hh

end Heisenberg.Exposure

end
end
end
end
end
end
end
end
end

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace Classical
namespace Heisenberg.MeshEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E]

end Heisenberg.MeshEnergy
namespace Heisenberg.MeshPair
open MeshEnergy
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {V : Type*} [Fintype V] [DecidableEq V]

end Heisenberg.MeshPair

namespace Heisenberg.MeshPair
open scoped RealInnerProductSpace Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

end Heisenberg.MeshPair

namespace Heisenberg.MatrixContraction

variable {V : Type*} [Fintype V]

end Heisenberg.MatrixContraction

namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction Matrix
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

end Heisenberg.MeshPair

namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

end Heisenberg.MeshPair

namespace Heisenberg.Serial
open Matrix Heisenberg.MeshPair
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]

end Heisenberg.Serial

namespace Heisenberg.Serial
open Matrix Heisenberg.Hitting
variable {V : Type*} [Fintype V] [DecidableEq V]

end Heisenberg.Serial

namespace Heisenberg.Exposure
open Matrix
open scoped BigOperators
variable {T B V : Type*} [Fintype T] [Fintype B] [Fintype V]

lemma productWeight_coordinate (w : T → B → ℝ) (hw : ∀ t, ∑ b,w t b = 1)
    (t : T) (F : B → ℝ) :
    (∑ c : T → B,productWeight w c * F (c t)) = ∑ b,w t b * F b := by
  classical
  let w' : T → B → ℝ := Function.update w t (fun b => w t b * F b)
  have he : ∀ c,productWeight w c * F (c t) = productWeight w' c := by
    intro c
    have hh : (fun i => w' i (c i)) = Function.update (fun i => w i (c i)) t
        (w t (c t) * F (c t)) := by
      funext i
      by_cases hi : i = t <;> simp [w',hi]
    rw [productWeight,productWeight,hh,Finset.prod_update_of_mem (Finset.mem_univ t)]
    rw [←Finset.mul_prod_erase Finset.univ (fun i => w i (c i)) (Finset.mem_univ t)]
    rw [Finset.erase_eq]
    ring
  simp_rw [he,productWeight]
  rw [←Fintype.prod_sum]
  rw [Finset.prod_eq_single t]
  · simp [w']
  · intro i _ hi
    simpa [w',hi] using hw i
  · simp

lemma mean_residual_coordinate (w : T → Bool → ℝ) (hw : ∀ t, ∑ b,w t b=1)
    (M : T → Prop) [DecidablePred M] (base : T → Bool) (t : T) (F : Bool → ℝ) :
    (∑ c : T → Bool,productWeight w c * F (if M t then base t else c t)) =
      if M t then F (base t) else ∑ b,w t b * F b := by
  by_cases ht : M t
  · simp only [ite_eq_left ht,←Finset.sum_mul,productWeight_sum w hw,one_mul]
  · simp only [ite_eq_right ht]
    exact productWeight_coordinate w hw t F

def layerKernel (s : Equiv.Perm T) (σ : T → Bool → Equiv.Perm V)
    (w : T → Bool → ℝ) : Matrix (T × V) (T × V) ℝ := fun z x =>
  if z.1 = s x.1 then ∑ b,w x.1 b * if z.2 = σ x.1 b x.2 then 1 else 0 else 0

omit [Fintype V] in

theorem mean_layer_wiring
    (s : Equiv.Perm T) (σ : T → Bool → Equiv.Perm V)
    (w : T → Bool → ℝ) (hw : ∀ t,∑ b,w t b=1) :
    (∑ c : T → Bool,productWeight w c •
      (LayeredExchange.wiring s (fun t => σ t (c t))).permMatrix ℝ :
        Matrix (T × V) (T × V) ℝ).transpose =
        layerKernel s σ w := by
  ext ⟨u,a⟩ ⟨t,b⟩
  simp only [Matrix.transpose_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,Option.mem_some_iff]
  simp only [LayeredExchange.wiring_apply,Prod.mk.injEq]
  by_cases hu : u = s t
  · simpa only [hu,true_and,layerKernel,↓reduceIte,eq_comm] using
      productWeight_coordinate w hw t (fun c => if a=σ t c b then 1 else 0)
  · simp [hu,Ne.symm hu,layerKernel]

lemma layerKernel_backward (s : Equiv.Perm T) (σ : T → Bool → Equiv.Perm V)
    (w : T → Bool → ℝ) (f : T × V → ℝ) (t : T) (v : V) :
    ((layerKernel s σ w).transpose *ᵥ f) (t,v) =
      ∑ b,w t b * f (s t,σ t b v) := by
  classical
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Fintype.sum_prod_type,layerKernel]
  rw [Finset.sum_eq_single (s t)]
  · simp only [↓reduceIte,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_eq_single (σ t b v)]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  · intro u _ hu
    simp [hu]
  · simp

end Heisenberg.Exposure

@[reducible] local instance kernelDecEq (α : Type*) : DecidableEq α := Classical.decEq α

namespace Heisenberg.Exposure
open Heisenberg.Serial Heisenberg.MeshPair
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma residualBetween_mean {n : ℕ} (p : Fin n → ℝ) (M : Fin n → Prop)
    (base : Fin n → Bool) (D E : Set V) (a b : V) (t : Fin n) (x y : V) :
    (∑ c : Fin n → Bool,productWeight (fun i z => if z then p i else 1-p i) c *
      killedBetween D E (if residualCoins M base c t then Equiv.swap a b else 1) x y) =
      residualBetween D E (M t) (base t) a b (p t) x y := by
  have h := mean_residual_coordinate (fun i z => if z then p i else 1-p i)
    (by intro i; simp) M base t
    (fun z => killedBetween D E (if z then Equiv.swap a b else 1) x y)
  change (∑ c,productWeight _ c *
    (fun z => killedBetween D E (if z then Equiv.swap a b else 1) x y)
      (if M t then base t else c t)) = _
  have hu : @Finset.univ (Fin n → Bool)
    (@Pi.instFintype (Fin n) (fun _ => Bool) (fun a b => Classical.propDecidable (a=b))
      (Fin.fintype n) (fun _ => Bool.fintype)) = (Finset.univ : Finset (Fin n → Bool)) := by
    ext c
    simp
  rw [hu] at h
  refine h.trans ?_
  by_cases ht : M t
  · simp only [residualBetween,ite_eq_left ht]
  · simp [ht,residualBetween,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_comm]

omit [Fintype V] in

theorem killed_residual_cyclic (n : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (M : Fin (n+1) → Prop) (base : Fin (n+1) → Bool) (D : Fin (n+1) → Set V) :
    killedMean (productWeight (fun i z => if z then p i else 1-p i))
      (fun c => layerHistory (finRotate (n+1)) (fun i => Equiv.swap (a i) (b i))
        (residualCoins M base c)) {z | z.2∈D z.1} =
      cyclicKernel n (fun i => residualBetween (D i) (D (finRotate (n+1) i))
        (M i) (base i) (a i) (b i) (p i)) := by
  ext ⟨u,x⟩ ⟨t,y⟩
  simp only [killedMean,Set.mem_ofPred_eq,layerHistory,LayeredExchange.wiring_apply,Prod.mk.injEq,cyclicKernel]
  by_cases hu : u=finRotate (n+1) t
  · subst u
    simp only [true_and,ite_true]
    symm
    refine (residualBetween_mean p M base (D t) (D (finRotate (n+1) t)) (a t) (b t) t x y).symm.trans ?_
    by_cases hD : x∈D (finRotate (n+1) t) ∧ y∈D t
    · simp only [ite_eq_left hD]
      apply Finset.sum_congr rfl
      intro c _
      simp only [killedBetween,hD.1,hD.2,true_and]
    · simp only [ite_eq_right hD]
      apply Finset.sum_eq_zero
      intro c _
      have hn : ¬(y∈D t ∧ x∈D (finRotate (n+1) t) ∧ x=(if residualCoins M base c t then Equiv.swap (a t) (b t) else 1) y) :=
        fun h => hD ⟨h.2.1,h.1⟩
      simp only [killedBetween,ite_eq_right hn,mul_zero]
  · simp only [hu,false_and,ite_false,mul_zero,Finset.sum_const_zero,ite_self]

end Heisenberg.Exposure
end
end

end OAI
