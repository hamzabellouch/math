import OAI.MathematicalPhysics.Heisenberg.MeanLeakage

namespace OAI

noncomputable section

open Filter Topology
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped BigOperators Classical

open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] lemma euclideanMap_one : euclideanMap (1 : Matrix V V ℝ) = LinearMap.id := by
  ext v i
  simp [euclideanMap_apply]

omit [DecidableEq V] in
lemma euclideanMap_mul (A B : Matrix V V ℝ) (v : EuclideanSpace ℝ V) :
    euclideanMap (A*B) v = euclideanMap A (euclideanMap B v) := by
  ext i
  change ((A*B).mulVec v.ofLp) i = (A.mulVec (B.mulVec v.ofLp)) i
  rw [Matrix.mulVec_mulVec]

lemma substochastic_one : DoublySubstochastic (1 : Matrix V V ℝ) := by
  constructor
  · intro i j; simp only [Matrix.one_apply]; split_ifs <;> norm_num
  · intro i
    change (∑ j, if i=j then (1:ℝ) else 0)≤1
    simp
  · intro i
    change (∑ j, if j=i then (1:ℝ) else 0)≤1
    simp

def prefixMatrix (K : ℕ → Matrix V V ℝ) : ℕ → Matrix V V ℝ
  | 0 => 1
  | n+1 => K n*prefixMatrix K n

lemma prefix_substochastic (K : ℕ → Matrix V V ℝ) (n : ℕ)
    (hK : ∀ i,i<n → DoublySubstochastic (K i)) : DoublySubstochastic (prefixMatrix K n) := by
  induction n with
  | zero => exact substochastic_one
  | succ n ih => exact (hK n (by omega)).mul (ih (fun i hi=>hK i (by omega)))

lemma prefix_add (K : ℕ → Matrix V V ℝ) (m n : ℕ) :
    prefixMatrix K (m+n)=prefixMatrix (fun i=>K (m+i)) n*prefixMatrix K m := by
  induction n with
  | zero => simp [prefixMatrix]
  | succ n ih =>
    change K (m+n)*prefixMatrix K (m+n)=(K (m+n)*prefixMatrix (fun i=>K (m+i)) n)*prefixMatrix K m
    rw [ih,Matrix.mul_assoc]

omit [DecidableEq V] in
lemma euclideanMap_bounds (A : Matrix V V ℝ) (hA : DoublySubstochastic A)
    (f : EuclideanSpace ℝ V) (hf : ∀ i,0≤f.ofLp i ∧ f.ofLp i≤1) :
    ∀ i,0≤(euclideanMap A f).ofLp i ∧ (euclideanMap A f).ofLp i≤1 := by
  intro i
  simp only [euclideanMap_apply,Matrix.mulVec,dotProduct]
  constructor
  · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hA.nonneg i j) (hf j).1)
  · calc
      _ ≤ ∑ j,A i j*1 := Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hf j).2 (hA.nonneg i j))
      _ ≤ 1 := by simpa using hA.row i

lemma pairing_columns (A : Matrix V V ℝ) (J : Finset V) (f : EuclideanSpace ℝ V) :
    ⟪euclideanMap A (WithLp.toLp 2 (fun j=>if j∈J then (1:ℝ) else 0)),f⟫ =
      ∑ j∈J,∑ i,A i j*f.ofLp i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, f.ofLp i*(A.mulVec (fun j=>if j∈J then (1:ℝ) else 0) i))=_
  simp only [Matrix.mulVec,dotProduct,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_mem,Finset.univ_inter,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end Heisenberg.MeshPair

namespace Heisenberg.Exposure
open Heisenberg.MeshPair Heisenberg.MatrixContraction
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] in
lemma exposedSweep_prefix (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) (n : ℕ)
    (v : EuclideanSpace ℝ V) :
    exposedSweep s a b base P I p r n v =
      euclideanMap (prefixMatrix (fun i=>exposedStep s a b base P I p (r i)) n) v := by
  induction n with
  | zero => simp [exposedSweep,prefixMatrix]
  | succ n ih => rw [exposedSweep,prefixMatrix,euclideanMap_mul,ih]

omit [Fintype T] in
lemma exposedSweep_add (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) (m n : ℕ)
    (v : EuclideanSpace ℝ V) :
    exposedSweep s a b base P I p r (m+n) v =
      exposedSweep s a b base P I p (fun i=>r (m+i)) n
        (exposedSweep s a b base P I p r m v) := by
  simp only [exposedSweep_prefix,prefix_add,euclideanMap_mul]

omit [Fintype T] in
lemma exposedSweep_bounds (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1)
    (r : ℕ → T) (n : ℕ) (v : EuclideanSpace ℝ V)
    (hv : ∀ i,0≤v.ofLp i ∧ v.ofLp i≤1) :
    ∀ i,0≤(exposedSweep s a b base P I p r n v).ofLp i ∧
      (exposedSweep s a b base P I p r n v).ofLp i≤1 := by
  rw [exposedSweep_prefix]
  exact euclideanMap_bounds _ (prefix_substochastic _ n (fun i _=>
    exposedStep_substochastic s a b base P I p hp (r i))) v hv

omit [Fintype T] in
lemma exposedSweep_supported (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) (n : ℕ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (v : EuclideanSpace ℝ V)
    (hv : ∀ j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I → v.ofLp j=0) :
    ∀ j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r n)∩I →
      (exposedSweep s a b base P I p r n v).ofLp j=0 := by
  cases n with
  | zero => exact hv
  | succ n =>
    intro j hj
    rw [hr n (by omega)] at hj
    exact residualBetween_supported _ _ _ _ _ _ _ _ j hj

end Heisenberg.Exposure

open scoped BigOperators Classical RealInnerProductSpace
open Filter Topology
namespace Heisenberg.MeshPair
variable {V : Type*} [Fintype V] [DecidableEq V]
lemma quietSweep_congr (H D : Set V) (a b c d : ℕ → V) (t : ℝ) (q : ℕ)
    (ha : ∀ i,i<q → a i=c i) (hb : ∀ i,i<q → b i=d i) (v : EuclideanSpace ℝ V) :
    quietSweep H D a b t q v=quietSweep H D c d t q v := by
  induction q with
  | zero => rfl
  | succ q ih => rw [quietSweep,quietSweep,ha q (by omega),hb q (by omega),
      ih (fun i hi=>ha i (by omega)) (fun i hi=>hb i (by omega))]
omit [Fintype V] [DecidableEq V] in
lemma quietEnergy_congr (H : Set V) (a b c d : ℕ → V) (q : ℕ)
    (ha : ∀ i,i<q → a i=c i) (hb : ∀ i,i<q → b i=d i) (v : EuclideanSpace ℝ V) :
    quietEnergy H a b q v=quietEnergy H c d q v := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [ha i (Finset.mem_range.mp hi),hb i (Finset.mem_range.mp hi)]
end Heisenberg.MeshPair
open scoped BigOperators Classical RealInnerProductSpace
open Filter Topology
namespace Heisenberg.Exposure
open Heisenberg.MeshPair
variable {V : Type} [Fintype V]

theorem fixed_sweep_energy (a₀ b₀ : ℕ → V) (q : ℕ)
    (hab : ∀ i,i<q → a₀ i≠b₀ i) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ),0≤t → t≤2 →
      ∀ (T : Type) [Fintype T] (s : Equiv.Perm T) (a b : T → V) (r : ℕ → T),
      (∀ i,i<q → r (i+1)=s (r i)) →
      (∀ i,i<q → a (r i)=a₀ i) → (∀ i,i<q → b (r i)=b₀ i) →
      ∀ (p : T → ℝ) (_hp : ∀ i,0≤p i ∧ p i≤1) (_hrate : ∀ i,i<q → p (r i)=t/2)
        (P : Set (T×V)) (I : Set V) (v : (T → Bool) → EuclideanSpace ℝ V),
      (∀ base j,0≤(v base).ofLp j ∧ (v base).ofLp j≤1) →
      (∀ base j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I →
        (v base).ofLp j=0) →
      (∑ base,layerMass s a b P p base *
        (t*MeshPair.quietEnergy (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0))
          a₀ b₀ q (v base))) ≤
        (∑ base,layerMass s a b P p base *
          (‖v base‖^2-‖exposedSweep s a b base P I p r q (v base)‖^2))+
        ε*t*Fintype.card V+t^2*q^2 := by
  filter_upwards [quietSweep_energy a₀ b₀ q hab hε] with t ht
  intro ht0 _ht2 T _ s a b r hr ha hb p hp hrate P I v hv hvI
  have hab' : ∀ i,i<q → a (r i)≠b (r i) := by
    intro i hi
    rw [ha i hi,hb i hi]
    exact hab i hi
  have hl (base : T → Bool) : t*MeshPair.quietEnergy
      (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)) a₀ b₀ q (v base) ≤
      ‖v base‖^2-‖exposedSweep s a b base P I p r q (v base)‖^2+
        ε*t*‖v base‖^2+(if ∃ i,i<q ∧ base (r i)=true then t*q else 0) := by
    have hc := exposedSweep_contraction s a b base P I p hp r q (v base)
    have hn : 0≤‖v base‖^2-‖exposedSweep s a b base P I p r q (v base)‖^2 := by
      nlinarith [norm_nonneg (v base),norm_nonneg (exposedSweep s a b base P I p r q (v base))]
    by_cases hnon : ∃ i,i<q ∧ base (r i)=true
    · rw [ite_eq_left hnon]
      have he := mul_le_mul_of_nonneg_left
        (quietEnergy_le_card (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0))
          a₀ b₀ q (v base) (hv base)) ht0
      have hz : 0≤ε*t*‖v base‖^2 := by positivity
      linarith
    · rw [ite_eq_right hnon]
      have hquiet : ∀ i,i<q → base (r i)=false := by
        intro i hi
        cases he : base (r i)
        · rfl
        · exact (hnon ⟨i,hi,he⟩).elim
      have heq := exposedSweep_coins s a b base P I p (fun _=>t/2) r q hrate (v base)
      rw [heq,exposedSweep_quiet s a b base P I r q t hr hquiet hab' (v base),
        quietSweep_congr _ _ (a ∘ r) (b ∘ r) a₀ b₀ t q ha hb]
      have he := (abs_le.mp (ht (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)) (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I) (v base) (hvI base))).2
      rw [abs_of_nonneg ht0] at he
      linarith
  have hs := layerMass_sum s a b P p hp
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun base _=>
    mul_le_mul_of_nonneg_left (hl base) (layerMass_nonneg s a b P p hp base))
  have he : (∑ base,layerMass s a b P p base*(ε*t*‖v base‖^2))≤
      ε*t*Fintype.card V := by
    calc
      _ ≤ ∑ base,layerMass s a b P p base*(ε*t*Fintype.card V) :=
        Finset.sum_le_sum (fun base _=>mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (bounded_euclidean_sq (v base) (hv base)) (by positivity))
            (layerMass_nonneg s a b P p hp base))
      _ = _ := by rw [←Finset.sum_mul,hs,one_mul]
  have hn := tilted_nonquiet_error s a b P p hp r q ht0 hrate
  simp only [mul_add,Finset.sum_add_distrib] at h
  linarith

lemma exposedSweep_norm_antitone {T : Type} [Fintype T]
    (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (hp : ∀ j,0≤p j ∧ p j≤1)
    (r : ℕ → T) {m n : ℕ} (hmn : m≤n) (v : EuclideanSpace ℝ V) :
    ‖exposedSweep s a b base P I p r n v‖≤‖exposedSweep s a b base P I p r m v‖ := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [exposedSweep_add]
  exact exposedSweep_contraction s a b base P I p hp _ _ _

theorem round_energy (a₀ b₀ : ℕ → V) (q : ℕ)
    (hab : ∀ j,j<q → a₀ j≠b₀ j) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ),0≤t → t≤2 →
      ∀ (T : Type) [Fintype T] (s : Equiv.Perm T) (a b : T → V)
        (r : ℕ → T) (c : ℕ → ℕ),
      (∀ j,r (j+1)=s (r j)) → (∀ i,c i+q≤c (i+1)) →
      (∀ i j,j<q → a (r (c i+j))=a₀ j) →
      (∀ i j,j<q → b (r (c i+j))=b₀ j) →
      ∀ (p : T → ℝ) (_hp : ∀ j,0≤p j ∧ p j≤1)
        (_hrate : ∀ i j,j<q → p (r (c i+j))=t/2)
        (P : Set (T×V)) (I : Set V) (f : (T → Bool) → EuclideanSpace ℝ V),
      (∀ base j,0≤(f base).ofLp j ∧ (f base).ofLp j≤1) →
      (∀ base j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I →
        (f base).ofLp j=0) →
      ∀ i, t*(∑ base,layerMass s a b P p base *
        MeshPair.quietEnergy (holeCut s (fun j=>Equiv.swap (a j) (b j)) base P (r (c i)))
          a₀ b₀ q (exposedSweep s a b base P I p r (c i) (f base))) ≤
        (∑ base,layerMass s a b P p base *
          (‖exposedSweep s a b base P I p r (c i) (f base)‖^2-
            ‖exposedSweep s a b base P I p r (c (i+1)) (f base)‖^2))+
        ε*t*Fintype.card V+t^2*q^2 := by
  filter_upwards [fixed_sweep_energy a₀ b₀ q hab hε] with t ht
  intro ht0 ht2 T _ s a b r c hr hc ha hb p hp hrate P I f hf hs i
  let v : (T → Bool) → EuclideanSpace ℝ V :=
    fun base=>exposedSweep s a b base P I p r (c i) (f base)
  have hv (base : T → Bool) : ∀ j,0≤(v base).ofLp j ∧ (v base).ofLp j≤1 :=
    exposedSweep_bounds s a b base P I p hp r (c i) (f base) (hf base)
  have hvI (base : T → Bool) : ∀ j,
      j∉holeCut s (fun j=>Equiv.swap (a j) (b j)) base P (r (c i))∩I → (v base).ofLp j=0 :=
    exposedSweep_supported s a b base P I p r (c i) (fun j _=>hr j) (f base) (hs base)
  have hseg : ∀ j,j<q → r (c i+(j+1))=s (r (c i+j)) := by
    intro j _
    simpa only [Nat.add_assoc] using hr (c i+j)
  have h := ht ht0 ht2 T s a b (fun j=>r (c i+j)) hseg (ha i) (hb i)
    p hp (hrate i) P I v hv (by simpa only [Nat.add_zero] using hvI)
  simp only [Nat.add_zero] at h
  have hcolon (base : T → Bool) :
      ‖exposedSweep s a b base P I p (fun j=>r (c i+j)) q (v base)‖^2 ≥
        ‖exposedSweep s a b base P I p r (c (i+1)) (f base)‖^2 := by
    change ‖exposedSweep s a b base P I p (fun j=>r (c i+j)) q
      (exposedSweep s a b base P I p r (c i) (f base))‖^2≥_
    rw [←exposedSweep_add]
    exact pow_le_pow_left₀ (norm_nonneg _) (exposedSweep_norm_antitone s a b base P I p hp r (hc i) (f base)) 2
  rw [Finset.mul_sum]
  have hrew : (∑ base,layerMass s a b P p base*(t*MeshPair.quietEnergy
      (holeCut s (fun j=>Equiv.swap (a j) (b j)) base P (r (c i))) a₀ b₀ q (v base)))=
      ∑ base,t*(layerMass s a b P p base*MeshPair.quietEnergy
      (holeCut s (fun j=>Equiv.swap (a j) (b j)) base P (r (c i))) a₀ b₀ q (v base)) := by
    apply Finset.sum_congr rfl
    intro base _
    ring
  rw [hrew] at h
  apply h.trans
  apply add_le_add _ (le_refl _)
  apply add_le_add _ (le_refl _)
  apply Finset.sum_le_sum
  intro base _
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (hcolon base) _) (layerMass_nonneg s a b P p hp base)

end Heisenberg.Exposure

end

end OAI
