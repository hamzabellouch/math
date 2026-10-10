import OAI.Probability.DilutedSpin.PhysicalShapeError
import OAI.Probability.DilutedSpin.QIntegration
import OAI.Probability.DilutedSpin.ReservoirRate
import OAI.Probability.DilutedSpin.RootDeviationDistance

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

noncomputable def reservoirShapeDeviation (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) : ℝ :=
  shapeDeviation
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (reservoirRate M.alpha (p-1) N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) S
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

lemma reservoirShapeDeviation_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    0≤reservoirShapeDeviation M C H N L u S := shapeDeviation_nonneg _ _ _ _ _

lemma reservoirShapeDeviation_distance (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (N L : ℕ) (hN : 0<N) (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    |physicalShapeDeviation M C H N L u S-reservoirShapeDeviation M C H N L u S|≤
      (2:ℝ)^S.leaves*(3*reservoirDistance M.alpha (p-1) N) := by
  apply root_shapeDeviation_distance
    (fullRoot_reservoirDistance _ _ _ _ _ hα (p-1) N hN)
    S _ _ _ _ _ _ (measurable_physicalBase M C H N)
    (fun y i => readVector_bound _ y i) (reservoirDistance_nonneg _ _ _)

lemma reservoirShape_qExpect_distance (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (N L : ℕ) (hN : 0<N) (u : Spec L×ℕ → ℝ) (k : ℕ) :
    |qExpect (grid (L+1) 0 (L+1)) (physicalShapeDeviation M C H N L u) k (single (L+1))-
      qExpect (grid (L+1) 0 (L+1)) (reservoirShapeDeviation M C H N L u) k (single (L+1))|≤
      (2:ℝ)^(k+1)*(3*reservoirDistance M.alpha (p-1) N) := by
  have hh := qExpect_difference_bound (grid (L+1) 0 (L+1))
    (grid_strictMono (by omega)).monotone grid_nonneg _ _ _
    (reservoirShapeDeviation_distance M hα C H N L hN u) k (single (L+1))
  apply hh.trans
  have h := qExpect_mono_leaves (grid (L+1) 0 (L+1))
    (grid_strictMono (by omega)).monotone grid_nonneg
    (fun S => (2:ℝ)^S.leaves*(3*reservoirDistance M.alpha (p-1) N))
    (fun _ => (2:ℝ)^(k+1)*(3*reservoirDistance M.alpha (p-1) N)) k (single (L+1))
    (fun S hS => by rw [hS,leaves_single,Nat.add_comm 1 k])
  have hz : grid (L+1) 0 (L+1) 0=0 := by simp [grid]
  simpa only [qExpect_const _ hz (grid_last (by omega : 0<L+1))] using h

lemma reservoirShape_qExpect_difference_tendsto (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (L : ℕ) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (us : ℕ → Spec L×ℕ → ℝ)
    (k : ℕ) :
    Tendsto (fun n => qExpect (grid (L+1) 0 (L+1))
      (physicalShapeDeviation M C H (Ns n+1) L (us n)) k (single (L+1))-
      qExpect (grid (L+1) 0 (L+1))
      (reservoirShapeDeviation M C H (Ns n+1) L (us n)) k (single (L+1))) atTop (𝓝 0) := by
  have hd := (reservoirDistance_tendsto M.alpha hα (p-1)).comp
    (tendsto_add_atTop_nat 1 |>.comp hNs)
  have hh := (hd.const_mul 3).const_mul ((2:ℝ)^(k+1))
  simp only [mul_zero,Function.comp_apply] at hh
  exact squeeze_zero_norm (fun n : ℕ => by simpa only [Real.norm_eq_abs] using
      (reservoirShape_qExpect_distance M hα C H (Ns n+1) L (by omega) (us n) k)) hh

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass.KernelTower
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]

noncomputable def piTower : (n : ℕ) → (ι → KernelTower Ω n) → KernelTower (ι → Ω) n
  | 0,_ => ()
  | n+1,T => (FiniteLaw.pi (fun i => (T i).1),fun x => piTower n (fun i => (T i).2 (x i)))

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {ι Ω : Type}

def sampleMap (f : Ω → ι) : {n : ℕ} → (S : PrescribedTree n) → Sample Ω S → Sample ι S
  | 0,.leaf,_ => ()
  | _+1,.node _ C,x => fun i => (f (x i).1,sampleMap f (C i) (x i).2)

@[simp] lemma pathAt_sampleMap (f : Ω → ι) {n : ℕ} (S : PrescribedTree n)
    (a : S.Leaf) (x : Sample Ω S) :
    S.pathAt a (sampleMap f S x)=KernelTower.pathMap f n (S.pathAt a x) := by
  induction S with
  | leaf => rfl
  | node k C ih => exact congrArg (Prod.mk _) (ih a.1 a.2 (x a.1).2)

def samplePi : {n : ℕ} → (S : PrescribedTree n) → (ι → Sample Ω S) → Sample (ι → Ω) S
  | 0,.leaf,_ => ()
  | _+1,.node _ C,x => fun j => (fun i => (x i j).1,samplePi (C j) (fun i => (x i j).2))

@[simp] lemma sampleMap_pi {n : ℕ} (S : PrescribedTree n) (x : ι → Sample Ω S) (i : ι) :
    sampleMap (fun y : ι → Ω => y i) S (samplePi S x)=x i := by
  induction S with
  | leaf => change () = x i; exact Subsingleton.elim _ _
  | node k C ih =>
    funext j
    change ((x i j).1,sampleMap (fun y : ι → Ω => y i) (C j) (samplePi (C j) (fun i => (x i j).2)))=x i j
    rw [ih]

@[simp] lemma samplePi_eval {n : ℕ} (S : PrescribedTree n) (x : Sample (ι → Ω) S) :
    samplePi S (fun i => sampleMap (fun y : ι → Ω => y i) S x)=x := by
  induction S with
  | leaf => change () = x; exact Subsingleton.elim _ _
  | node k C ih =>
    funext j
    change ((fun i => (x j).1 i),samplePi (C j) (fun i => sampleMap (fun y : ι → Ω => y i) (C j) (x j).2))=x j
    rw [ih]

def samplePiEquiv {n : ℕ} (S : PrescribedTree n) : Sample (ι → Ω) S ≃ (ι → Sample Ω S) where
  toFun x i := sampleMap (fun y : ι → Ω => y i) S x
  invFun := samplePi S
  left_inv := samplePi_eval S
  right_inv x := funext (sampleMap_pi S x)

variable [Fintype ι] [DecidableEq ι] [Fintype Ω]

lemma sampleLaw_piTower_weight {n : ℕ} (S : PrescribedTree n)
    (T : ι → KernelTower Ω n) (x : Sample (ι → Ω) S) :
    (S.sampleLaw (KernelTower.piTower n T)).weight x =
      ∏ i,(S.sampleLaw (T i)).weight (sampleMap (fun y : ι → Ω => y i) S x) := by
  induction S with
  | leaf => simp [sampleLaw,KernelTower.unitLaw]
  | @node n k C ih =>
    change (∏ j, (∏ i,(T i).1.weight ((x j).1 i))*
      ((C j).sampleLaw (KernelTower.piTower n (fun i => (T i).2 ((x j).1 i)))).weight (x j).2) =
      ∏ i,∏ j,(T i).1.weight ((x j).1 i)*
        ((C j).sampleLaw ((T i).2 ((x j).1 i))).weight (sampleMap (fun y : ι → Ω => y i) (C j) (x j).2)
    simp_rw [ih,← Finset.prod_mul_distrib]
    exact Finset.prod_comm

lemma sampleExpect_piTower {n : ℕ} (S : PrescribedTree n)
    (T : ι → KernelTower Ω n) (f : Sample (ι → Ω) S → ℝ) :
    (S.sampleLaw (KernelTower.piTower n T)).expect f =
      (FiniteLaw.pi (fun i => S.sampleLaw (T i))).expect (fun x => f (samplePi S x)) := by
  unfold FiniteLaw.expect
  apply Fintype.sum_equiv (samplePiEquiv S)
  intro x
  simp only [samplePiEquiv,Equiv.coe_fn_mk,samplePi_eval,FiniteLaw.pi,sampleLaw_piTower_weight]

lemma sampleExpect_pi_product {n : ℕ} (S : PrescribedTree n)
    (T : ι → KernelTower Ω n) (F : ι → Sample Ω S → ℝ) :
    (S.sampleLaw (KernelTower.piTower n T)).expect
      (fun x => ∏ i,F i (sampleMap (fun y : ι → Ω => y i) S x)) =
      ∏ i,(S.sampleLaw (T i)).expect (F i) := by
  rw [sampleExpect_piTower]
  simp only [sampleMap_pi]
  exact FiniteLaw.expect_pi_product _ _

end DilutedSpinGlass.PrescribedTree

end

end OAI
