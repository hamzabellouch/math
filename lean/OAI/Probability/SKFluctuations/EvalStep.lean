import Mathlib
import OAI.Probability.SKFluctuations.Bounds

namespace OAI

/-! Eval Step. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem Placement.eval_step {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)} {T : ReplicaTree ι S tail}
    (p : Placement T) (m : ℝ) (q : ι → ℝ≥0) (ha : OrderedSteps m tail)
    (P : T.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    (p.step (m,q)).eval w φ P B x = shiftedMean (Measure.pi fun j => gaussianReal 0 (q j)) m
      (gaussianHierarchy w φ tail) (p.eval w φ P B) x := by
  exact expect_step hw φ p.tree m q ha _ x

 theorem rowList_map_step {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)} {T : ReplicaTree ι S tail}
    (ps : List (Placement T)) (m : ℝ) (q : ι → ℝ≥0) (ha : OrderedSteps m tail)
    (P : T.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    rowList w φ (ps.map (Placement.step (m,q))) P B x =
      shiftedMean (Measure.pi fun j => gaussianReal 0 (q j)) m
        (gaussianHierarchy w φ tail) (rowList w φ ps P B) x := by
  induction ps with
  | nil => simp [rowList,shiftedMean,tiltedMean]
  | cons p ps ih =>
    change p.coeff*(p.step (m,q)).eval w φ P B x+rowList w φ (ps.map (Placement.step (m,q))) P B x =
      shiftedMean _ m _ (fun y => p.coeff*p.eval w φ P B y+rowList w φ ps P B y) x
    have hp : BddSmooth 0 (p.eval w φ P B) := p.tree.expect_smooth hw φ ha _ 0
    rw [Placement.eval_step hw φ p m q ha,ih,
      shiftedMean_add (hp.const_mul p.coeff)
        (rowList_smooth hw φ ps ha P B 0) (gaussianHierarchy_integrable hw φ tail ha m q x),
      shiftedMean_const_mul]

 theorem row_step {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)} (T : ReplicaTree ι S tail)
    (m : ℝ) (q : ι → ℝ≥0) {a : ℝ} (ha : OrderedSteps a ((m,q)::tail))
    (P : T.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    (T.step (m,q)).row w φ a P B x =
      (a-m)*(T.step (m,q)).expect w φ P x*gaussianHierarchyMean w φ B ((m,q)::tail) x +
      shiftedMean (Measure.pi fun j => gaussianReal 0 (q j)) m (gaussianHierarchy w φ tail)
        (T.row w φ m P B) x := by
  change (a-m)*(Placement.fresh (T.step (m,q)) (a-m)).eval w φ P B x+
    rowList w φ ((T.attach m).map (Placement.step (m,q))) P B x = _
  rw [Placement.eval_fresh hw φ _ ha,rowList_map_step hw φ _ m q ha.2.2.2]
  have hr : T.row w φ m P B = rowList w φ (T.attach m) P B := rfl
  rw [hr]
  ring

 theorem row_fork {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : (T.fork U).Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    (T.fork U).row w φ a P B x =
      -a*(T.fork U).expect w φ P x*gaussianHierarchyMean w φ B steps x +
      U.expect w φ (fun τ => T.row w φ a (fun σ => P (σ,τ)) B x) x +
      T.expect w φ (fun σ => U.row w φ a (fun τ => P (σ,τ)) B x) x := by
  change -a*(Placement.fresh (T.fork U) (-a)).eval w φ P B x +
    rowList w φ (((T.attach a).map (Placement.left U))++((U.attach a).map (Placement.right T))) P B x = _
  rw [Placement.eval_fresh hw φ _ ha]
  have he {V : ReplicaTree ι S steps} (ps qs : List (Placement V)) (Q : V.Assignment → ℝ) :
      rowList w φ (ps++qs) Q B x = rowList w φ ps Q B x+rowList w φ qs Q B x := by
    simp only [rowList,List.map_append,List.sum_append]
  rw [he,rowList_map_left,rowList_map_right]
  dsimp only [row]
  ring

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem fork_derivative_algebra {A B : Type*} [Fintype A] [Fintype B]
    (WA RA : A → ℝ) (WB RB : B → ℝ) (P : A × B → ℝ) (a M : ℝ) :
    (∑ z : A × B, ((RA z.1-a*WA z.1*M)*WB z.2+WA z.1*(RB z.2-a*WB z.2*M))*P z) =
      (∑ τ, WB τ*(∑ σ, RA σ*P (σ,τ))) + (∑ σ, WA σ*(∑ τ, RB τ*P (σ,τ))) -
      2*a*(∑ z : A × B, WA z.1*WB z.2*P z)*M := by
  have he : (∑ τ, WB τ*(∑ σ, RA σ*P (σ,τ))) = ∑ σ, ∑ τ, RA σ*WB τ*P (σ,τ) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    ring
  rw [he]
  simp only [Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul,
    ← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

 

 theorem hasDerivAt_expect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => T.expect w φ P (x+s • v))
      (T.row w φ a P (fun σ => φ σ v) (x+t • v) -
        a*T.expect w φ P (x+t • v)*gaussianHierarchyMean w φ (fun σ => φ σ v) steps (x+t • v)) t := by
  classical
  induction T generalizing a x t with
  | leaf =>
    apply (gaussianHierarchyMean_hasDerivAt hw φ P [] ha x v t).congr_deriv
    have he : (∑ σ, spinWeight w φ (x+t • v) σ*P σ*φ σ v) =
        ∑ σ, spinWeight w φ (x+t • v) σ*(P σ*φ σ v) := by
      apply Finset.sum_congr rfl
      intro σ _
      ring
    simp only [row,rowList,attach,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Placement.coincide,one_mul,add_zero]
    rw [Placement.eval_fresh hw φ _ ha]
    simp only [Placement.fresh,Placement.eval,ReplicaTree.expect,ReplicaTree.weight,
      gaussianHierarchyResponse,gaussianHierarchyMean,he,id_eq]
    ring
  | @step st tail T ih =>
    rcases st with ⟨m,q⟩
    let ν := Measure.pi fun j => gaussianReal 0 (q j)
    let F := gaussianHierarchy w φ tail
    let M := gaussianHierarchyMean w φ (fun σ => φ σ v) tail
    let A := T.expect w φ P
    let R := T.row w φ m P (fun σ => φ σ v)
    have hi := gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q
    have hF := gaussianHierarchy_regular hw φ tail ha.2.2.2 0
    have hM : BddSmooth 0 M := gaussianHierarchyMean_smooth hw φ (fun σ => φ σ v) tail ha.2.2.2 0
    have hA : BddSmooth 0 A := T.expect_smooth hw φ ha.2.2.2 P 0
    have hR : BddSmooth 0 R := rowList_smooth hw φ (T.attach m) ha.2.2.2 P (fun σ => φ σ v) 0
    have hD : BddSmooth 0 (fun y => R y-m*A y*M y) := hR.sub ((hA.const_mul m).mul hM)
    obtain ⟨B,hB,hbM⟩ := hM.bound
    obtain ⟨C,hC,hbA⟩ := hA.bound
    obtain ⟨D,hD0,hbD⟩ := hD.bound
    obtain ⟨K,hK⟩ := hF.1
    have hd := hasDerivAt_shiftedMean hB (add_nonneg hC hD0) hK.continuous hM.continuous
      hA.continuous hD.continuous
      (fun y s => gaussianHierarchy_hasDerivAt hw φ tail ha.2.2.2 y v s)
      (ih ha.2.2.2 P) hbM (fun y => (hbA y).trans (by linarith))
      (fun y => (hbD y).trans (by linarith)) hi x t
    have he : (fun y => R y-m*A y*M y) = fun y => R y-m*(A y*M y) := by funext y; ring
    have hfun : (fun (s : ℝ) => (T.step (m,q)).expect w φ P (x+s • v)) =
        (fun s => shiftedMean ν m F A (x+s • v)) := by
      funext s
      exact expect_step hw φ T m q ha.2.2.2 P _
    rw [hfun]
    apply hd.congr_deriv
    rw [he,shiftedMean_sub hR ((hA.mul hM).const_mul m) (hi (x+t • v)),shiftedMean_const_mul,
      row_step hw φ T m q ha,expect_step hw φ T m q ha.2.2.2]
    change _ = (a-m)*shiftedMean ν m F A (x+t • v)*shiftedMean ν m F M (x+t • v) +
      shiftedMean ν m F R (x+t • v)-a*shiftedMean ν m F A (x+t • v)*shiftedMean ν m F M (x+t • v)
    ring
  | @fork steps T U ihT ihU =>
    let B := fun σ => φ σ v
    let y := x+t • v
    let M := gaussianHierarchyMean w φ B steps y
    have hdT (σ : T.Assignment) : HasDerivAt (fun s => T.weight w φ σ (x+s • v))
        (T.row w φ a (fun τ => if τ = σ then 1 else 0) B y-a*T.weight w φ σ y*M) t := by
      simpa only [expect_indicator] using ihT ha (fun τ => if τ = σ then 1 else 0) x t
    have hdU (σ : U.Assignment) : HasDerivAt (fun s => U.weight w φ σ (x+s • v))
        (U.row w φ a (fun τ => if τ = σ then 1 else 0) B y-a*U.weight w φ σ y*M) t := by
      simpa only [expect_indicator] using ihU ha (fun τ => if τ = σ then 1 else 0) x t
    have hd := HasDerivAt.fun_sum (fun (σ : T.Assignment × U.Assignment) (_ : σ ∈ Finset.univ) =>
      ((hdT σ.1).mul (hdU σ.2)).mul_const (P σ))
    apply hd.congr_deriv
    rw [fork_derivative_algebra (fun σ => T.weight w φ σ y)
      (fun σ => T.row w φ a (fun τ => if τ = σ then 1 else 0) B y)
      (fun σ => U.weight w φ σ y) (fun σ => U.row w φ a (fun τ => if τ = σ then 1 else 0) B y) P a M]
    have hT (τ : U.Assignment) : (∑ σ, T.row w φ a (fun ζ => if ζ = σ then 1 else 0) B y*P (σ,τ)) =
        T.row w φ a (fun σ => P (σ,τ)) B y := rowList_indicator_expand w φ (T.attach a) _ B y
    have hU (σ : T.Assignment) : (∑ τ, U.row w φ a (fun ζ => if ζ = τ then 1 else 0) B y*P (σ,τ)) =
        U.row w φ a (fun τ => P (σ,τ)) B y := rowList_indicator_expand w φ (U.attach a) _ B y
    simp_rw [hT,hU]
    rw [row_fork hw φ T U ha]
    change U.expect w φ (fun τ => T.row w φ a (fun σ => P (σ,τ)) B y) y +
      T.expect w φ (fun σ => U.row w φ a (fun τ => P (σ,τ)) B y) y -
      2*a*(T.fork U).expect w φ P y*M = _
    ring

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*}

 

def normalizedAttach {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ) :
    List (Placement T) := Placement.fresh T (-a)::T.attach a

 theorem normalizedAttach_mass {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ) :
    mass (T.normalizedAttach a) = 0 := by
  change -a+mass (T.attach a) = 0
  rw [attach_mass]
  ring

 theorem normalizedAttach_variation {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) : variation (T.normalizedAttach a) = 2*(T.leaves:ℝ) := by
  change |-a|+variation (T.attach a) = _
  rw [abs_neg,abs_of_nonneg ha.bounds.1,attach_variation T ha]
  ring

 theorem normalizedAttach_leaves {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (p : Placement T) (hp : p ∈ T.normalizedAttach a) : p.tree.leaves ≤ T.leaves+1 := by
  rcases List.mem_cons.mp hp with rfl|hp
  · simp only [Placement.fresh,ReplicaTree.leaves,single_leaves,le_refl]
  · exact attach_leaves T a p hp

variable [Fintype ι] [Fintype S]

noncomputable def sourceJet (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a : ℝ) :
    (vs : List (ι → ℝ)) → {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) →
      (T.Assignment → ℝ) → (ι → ℝ) → ℝ
  | [], _, T, P, x => T.expect w φ P x
  | v::vs, _, T, P, x => ((T.normalizedAttach a).map fun p =>
      p.coeff*sourceJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x).sum

variable [Nonempty S]

 theorem sourceJet_single {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (v x : ι → ℝ) :
    sourceJet w φ a [v] T P x = T.row w φ a P (fun σ => φ σ v) x-
      a*T.expect w φ P x*gaussianHierarchyMean w φ (fun σ => φ σ v) steps x := by
  change -a*(Placement.fresh T (-a)).eval w φ P (fun σ => φ σ v) x +
    rowList w φ (T.attach a) P (fun σ => φ σ v) x = _
  rw [Placement.eval_fresh hw φ T ha]
  change -a*(_*_)+T.row w φ a P (fun σ => φ σ v) x = _
  ring

 theorem sourceJet_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (vs : List (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (r : ℕ) : BddSmooth r (sourceJet w φ a vs T P) := by
  induction vs generalizing T with
  | nil => exact T.expect_smooth hw φ ha P r
  | cons v vs ih =>
    have h (ps : List (Placement T)) : BddSmooth r (fun x => (ps.map fun p =>
        p.coeff*sourceJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x).sum) := by
      induction ps with
      | nil => exact BddSmooth.const r 0
      | cons p ps ihp => exact ((ih p.tree _).const_mul p.coeff).add ihp
    exact h _

 theorem sourceJet_hasDerivAt {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (vs : List (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (u x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => sourceJet w φ a vs T P (x+s • u))
      (sourceJet w φ a (vs++[u]) T P (x+t • u)) t := by
  induction vs generalizing T with
  | nil =>
    rw [List.nil_append,sourceJet_single hw φ T ha]
    exact hasDerivAt_expect hw φ u T ha P x t
  | cons v vs ih =>
    have h (ps : List (Placement T)) : HasDerivAt (fun s => (ps.map fun p =>
        p.coeff*sourceJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) (x+s • u)).sum)
        ((ps.map fun p => p.coeff*sourceJet w φ a (vs++[u]) p.tree
          (fun σ => P (p.restrict σ)*φ (p.spin σ) v) (x+t • u)).sum) t := by
      induction ps with
      | nil => exact hasDerivAt_const t 0
      | cons p ps ihp => exact ((ih p.tree _).const_mul p.coeff).add ihp
    exact h _

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*}

 
def attachmentCount (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => 2*r*attachmentCount (r+1) k

 theorem list_weight_abs_le {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (ps : List (Placement T)) (f : Placement T → ℝ) {C : ℝ}
    (hf : ∀ p ∈ ps, |f p| ≤ C) : |(ps.map fun p => p.coeff*f p).sum| ≤ variation ps*C := by
  induction ps with
  | nil => simp [variation]
  | cons p ps ih =>
    have h1 := hf p (List.mem_cons_self ..)
    have h2 := ih (fun q hq => hf q (List.mem_cons_of_mem p hq))
    change |p.coeff*f p+(ps.map fun q => q.coeff*f q).sum| ≤ _
    calc
      _ ≤ |p.coeff*f p|+|(ps.map fun q => q.coeff*f q).sum| := abs_add_le _ _
      _ ≤ |p.coeff| *C+variation ps*C := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
      _ = _ := by simp only [variation,List.map_cons,List.sum_cons]; ring

variable [Fintype ι] [Fintype S] [Nonempty S]

 

 theorem sourceJet_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (vs : List (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {r : ℕ} (hT : T.leaves ≤ r) {P : T.Assignment → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ v ∈ vs, ∀ σ, |φ σ v| ≤ D) (x : ι → ℝ) :
    |sourceJet w φ a vs T P x| ≤ (attachmentCount r vs.length:ℝ)*C*D^vs.length := by
  induction vs generalizing T r C with
  | nil => simpa only [sourceJet,List.length_nil,attachmentCount,pow_zero,Nat.cast_one,mul_one,one_mul]
      using T.expect_abs_le hw φ ha hP x
  | cons v vs ih =>
    let L := (attachmentCount (r+1) vs.length:ℝ)*(C*D)*D^vs.length
    have hL : 0 ≤ L := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC hD)) (pow_nonneg hD _)
    have hp (p : Placement T) (hp : p ∈ T.normalizedAttach a) :
        |sourceJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x| ≤ L := by
      apply ih p.tree ((normalizedAttach_leaves T a p hp).trans (Nat.add_le_add_right hT 1))
        (mul_nonneg hC hD)
      · intro σ
        rw [abs_mul]
        exact mul_le_mul (hP _) (hB v (List.mem_cons_self ..) _) (abs_nonneg _) hC
      · exact fun u hu => hB u (List.mem_cons_of_mem v hu)
    have hs := list_weight_abs_le (T.normalizedAttach a)
      (fun p => sourceJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x) hp
    rw [normalizedAttach_variation T ha] at hs
    calc
      |sourceJet w φ a (v::vs) T P x| ≤ 2*(T.leaves:ℝ)*L := hs
      _ ≤ 2*(r:ℝ)*L := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hT) (by norm_num)) hL
      _ = _ := by simp only [L,List.length_cons,attachmentCount,Nat.cast_mul,Nat.cast_ofNat,pow_succ]; ring

 theorem sourceJet_two_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) {P : T.Assignment → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : ∀ σ, |P σ| ≤ C) (v : ι → ℝ)
    (hB : ∀ σ, |φ σ v| ≤ D) (x : ι → ℝ) :
    |sourceJet w φ a [v,v] T P x| ≤ 4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*C*D^2 := by
  have h := sourceJet_abs_le hw φ [v,v] T ha (le_refl T.leaves) hC hD hP
    (fun u hu => by
      have huv : u = v := by simpa using hu
      simpa only [huv] using hB) x
  convert h using 1
  simp only [List.length_cons,List.length_nil,attachmentCount,
    Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,mul_one]
  ring

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

noncomputable def powerJet (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a : ℝ) :
    (vs : List (ι → ℝ)) → {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) →
      (T.Assignment → ℝ) → (ι → ℝ) → ℝ
  | [], _, T, P, x => T.expect w φ P x
  | v::vs, _, T, P, x => ((T.attach a).map fun p =>
      p.coeff*powerJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x).sum

 omit [Nonempty S] in
 theorem powerJet_single (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (v x : ι → ℝ) :
    powerJet w φ a [v] T P x = T.row w φ a P (fun σ => φ σ v) x := rfl

 theorem powerJet_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (vs : List (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (r : ℕ) : BddSmooth r (powerJet w φ a vs T P) := by
  induction vs generalizing T with
  | nil => exact T.expect_smooth hw φ ha P r
  | cons v vs ih =>
    have h (ps : List (Placement T)) : BddSmooth r (fun x => (ps.map fun p =>
        p.coeff*powerJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x).sum) := by
      induction ps with
      | nil => exact BddSmooth.const r 0
      | cons p ps ihp => exact ((ih p.tree _).const_mul p.coeff).add ihp
    exact h _

 
 theorem weighted_expect_hasDerivAt {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ)
    (v x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (a*gaussianHierarchy w φ steps (x+s • v))*T.expect w φ P (x+s • v))
      (Real.exp (a*gaussianHierarchy w φ steps (x+t • v))*powerJet w φ a [v] T P (x+t • v)) t := by
  apply ((((gaussianHierarchy_hasDerivAt hw φ steps ha x v t).const_mul a).exp).mul
    (hasDerivAt_expect hw φ v T ha P x t)).congr_deriv
  rw [powerJet_single]
  ring

 theorem weighted_powerJet_hasDerivAt {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (vs : List (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (u x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (a*gaussianHierarchy w φ steps (x+s • u))*powerJet w φ a vs T P (x+s • u))
      (Real.exp (a*gaussianHierarchy w φ steps (x+t • u))*powerJet w φ a (vs++[u]) T P (x+t • u)) t := by
  induction vs generalizing T with
  | nil => exact weighted_expect_hasDerivAt hw φ T ha P u x t
  | cons v vs ih =>
    have h (ps : List (Placement T)) : HasDerivAt (fun s => Real.exp (a*gaussianHierarchy w φ steps (x+s • u))*
        (ps.map fun p => p.coeff*powerJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) (x+s • u)).sum)
        (Real.exp (a*gaussianHierarchy w φ steps (x+t • u))*(ps.map fun p =>
          p.coeff*powerJet w φ a (vs++[u]) p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) (x+t • u)).sum) t := by
      induction ps with
      | nil => simpa only [List.map_nil,List.sum_nil,mul_zero] using hasDerivAt_const t (0:ℝ)
      | cons p ps ihp =>
        convert ((ih p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v)).const_mul p.coeff).add ihp using 1 <;>
          first | rfl | (funext s; simp only [List.map_cons,List.sum_cons,Pi.add_apply]; ring) |
            (simp only [List.map_cons,List.sum_cons]; ring)
    exact h _

 
 theorem powerJet_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (vs : List (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {r : ℕ} (hT : T.leaves ≤ r) {P : T.Assignment → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ v ∈ vs, ∀ σ, |φ σ v| ≤ D) (x : ι → ℝ) :
    |powerJet w φ a vs T P x| ≤ (attachmentCount r vs.length:ℝ)*C*D^vs.length := by
  induction vs generalizing T r C with
  | nil => simpa only [powerJet,attachmentCount,List.length_nil,pow_zero,Nat.cast_one,one_mul,mul_one] using
      T.expect_abs_le hw φ ha hP x
  | cons v vs ih =>
    let L := (attachmentCount (r+1) vs.length:ℝ)*(C*D)*D^vs.length
    have hL : 0 ≤ L := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC hD)) (pow_nonneg hD _)
    have hp (p : Placement T) (hp : p ∈ T.attach a) :
        |powerJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x| ≤ L := by
      apply ih p.tree ((attach_leaves T a p hp).trans (Nat.add_le_add_right hT 1)) (mul_nonneg hC hD)
      · intro σ
        rw [abs_mul]
        exact mul_le_mul (hP _) (hB v (List.mem_cons_self ..) _) (abs_nonneg _) hC
      · exact fun u hu => hB u (List.mem_cons_of_mem v hu)
    have hs := list_weight_abs_le (T.attach a)
      (fun p => powerJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x) hp
    rw [attach_variation T ha] at hs
    calc
      |powerJet w φ a (v::vs) T P x| ≤ (2*(T.leaves:ℝ)-a)*L := hs
      _ ≤ 2*(r:ℝ)*L := mul_le_mul_of_nonneg_right
        (by have h := Nat.cast_le (α := ℝ).mpr hT; have h0 := ha.bounds.1; linarith) hL
      _ = _ := by simp only [L,List.length_cons,attachmentCount,Nat.cast_mul,Nat.cast_ofNat,pow_succ]; ring

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem powerJet_one_eq {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (v x : ι → ℝ) :
    powerJet w φ a [v] T P x = sourceJet w φ a [v] T P x+
      a*T.expect w φ P x*gaussianHierarchyMean w φ (fun σ => φ σ v) steps x := by
  rw [powerJet_single,sourceJet_single hw φ T ha]
  ring

 
 theorem powerJet_two_eq {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (v x : ι → ℝ) :
    powerJet w φ a [v,v] T P x = sourceJet w φ a [v,v] T P x+
      2*a*sourceJet w φ a [v] T P x*gaussianHierarchyMean w φ (fun σ => φ σ v) steps x+
      T.expect w φ P x*(a*gaussianHierarchyResponse w φ (fun σ => φ σ v) v steps x+
        a^2*(gaussianHierarchyMean w φ (fun σ => φ σ v) steps x)^2) := by
  let F := gaussianHierarchy w φ steps
  let A := T.expect w φ P
  let M := gaussianHierarchyMean w φ (fun σ => φ σ v) steps
  let H := gaussianHierarchyResponse w φ (fun σ => φ σ v) v steps
  let J₁ := sourceJet w φ a [v] T P
  let J₂ := sourceJet w φ a [v,v] T P
  have hF : HasDerivAt (fun s : ℝ => F (x+s • v)) (M x) 0 := by
    simpa only [zero_smul,add_zero] using gaussianHierarchy_hasDerivAt hw φ steps ha x v 0
  have hA : HasDerivAt (fun s : ℝ => A (x+s • v)) (J₁ x) 0 := by
    simpa only [A,J₁,sourceJet,List.nil_append,zero_smul,add_zero] using sourceJet_hasDerivAt hw φ [] T ha P v x 0
  have hM : HasDerivAt (fun s : ℝ => M (x+s • v)) (H x) 0 := by
    simpa only [zero_smul,add_zero] using gaussianHierarchyMean_hasDerivAt hw φ (fun σ => φ σ v) steps ha x v 0
  have hJ : HasDerivAt (fun s : ℝ => J₁ (x+s • v)) (J₂ x) 0 := by
    simpa only [List.cons_append,List.nil_append,zero_smul,add_zero] using sourceJet_hasDerivAt hw φ [v] T ha P v x 0
  have hd := ((hF.const_mul a).exp).mul (hJ.add ((hA.const_mul a).mul hM))
  have hp := weighted_powerJet_hasDerivAt hw φ [v] T ha P v x 0
  simp_rw [powerJet_one_eq hw φ T ha] at hp
  simp only [List.cons_append,List.nil_append,zero_smul,add_zero] at hp hd
  have he := hp.unique hd
  apply (mul_left_cancel₀ (Real.exp_ne_zero (a*F x)))
  rw [he]
  dsimp only [F,A,M,H,J₁,J₂,Pi.add_apply,Pi.mul_apply] at *
  simp only [zero_smul,add_zero]
  ring

 theorem expect_const {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (x : ι → ℝ) :
    T.expect w φ (fun _ => c) x = c := by
  simp only [ReplicaTree.expect,← Finset.sum_mul,T.weight_sum hw φ ha,one_mul]

 theorem sourceJet_constant_one {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (v x : ι → ℝ) :
    sourceJet w φ a [v] T (fun _ => c) x = 0 := by
  have h := sourceJet_hasDerivAt hw φ [] T ha (fun _ => c) v x 0
  change HasDerivAt (fun s : ℝ => T.expect w φ (fun _ => c) (x+s • v))
    (sourceJet w φ a [v] T (fun _ => c) (x+0 • v)) 0 at h
  simp only [zero_smul,add_zero] at h
  simp_rw [expect_const hw φ T ha] at h
  exact h.unique (hasDerivAt_const 0 c)

 theorem sourceJet_constant_two {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (v x : ι → ℝ) :
    sourceJet w φ a [v,v] T (fun _ => c) x = 0 := by
  have h := sourceJet_hasDerivAt hw φ [v] T ha (fun _ => c) v x 0
  simp_rw [sourceJet_constant_one hw φ T ha] at h
  simp only [List.cons_append,List.nil_append,zero_smul,add_zero] at h
  exact h.unique (hasDerivAt_const 0 0)

 theorem powerJet_constant_two {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (v x : ι → ℝ) :
    powerJet w φ a [v,v] T (fun _ => 1) x =
      a*gaussianHierarchyResponse w φ (fun σ => φ σ v) v steps x+
        a^2*(gaussianHierarchyMean w φ (fun σ => φ σ v) steps x)^2 := by
  rw [powerJet_two_eq hw φ T ha,sourceJet_constant_one hw φ T ha,sourceJet_constant_two hw φ T ha,
    expect_const hw φ T ha]
  ring

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 

theorem productGaussian_conv (q r : ι → ℝ≥0) :
    (Measure.pi fun i => gaussianReal 0 (q i)) ∗
      (Measure.pi fun i => gaussianReal 0 (r i)) =
        Measure.pi fun i => gaussianReal 0 (q i+r i) := by
  have hadd (i : ι) : MeasurePreserving (fun p : ℝ × ℝ => p.1+p.2)
      ((gaussianReal 0 (q i)).prod (gaussianReal 0 (r i)))
      (gaussianReal 0 (q i+r i)) := by
    refine ⟨measurable_fst.add measurable_snd, ?_⟩
    change gaussianReal 0 (q i) ∗ gaussianReal 0 (r i) = _
    simpa only [zero_add] using (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0)
      (v₁ := q i) (v₂ := r i))
  have hpi := measurePreserving_pi _ _ hadd
  have hprod := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun i => gaussianReal 0 (q i)) (fun i => gaussianReal 0 (r i))
  have h := hpi.comp hprod.symm
  exact h.map_eq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 
theorem linearGaussian_conv (L : (ι → ℝ) →L[ℝ] E) (s t : ℝ≥0) :
    linearGaussian L s ∗ linearGaussian L t = linearGaussian L (s+t) := by
  rw [linearGaussian, linearGaussian, ← Measure.map_conv_continuousLinearMap,
    productGaussian_conv]
  rfl

 
theorem integral_linearGaussian_add (L : (ι → ℝ) →L[ℝ] E) (s t : ℝ≥0)
    {f : E → ℝ} (hf : Integrable f (linearGaussian L (s+t))) :
    (∫ z, f z ∂linearGaussian L (s+t)) =
      ∫ y, ∫ z, f (y+z) ∂linearGaussian L t ∂linearGaussian L s := by
  rw [← linearGaussian_conv] at hf ⊢
  exact integral_conv hf

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
 
theorem exp_mul_shiftedContinuation {ν : Measure E} [IsProbabilityMeasure ν]
    {m : ℝ} (hm : m ≠ 0) {F : E → ℝ} (x : E)
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    Real.exp (m*shiftedContinuation ν m F x) = ∫ z, Real.exp (m*F (x+z)) ∂ν := by
  rw [shiftedContinuation,mul_div_cancel₀ _ hm,Real.exp_log (partition_pos m hi)]

 
theorem shiftedContinuation_linearGaussian_add (L : (ι → ℝ) →L[ℝ] E)
    {F : E → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) {m : ℝ} (hm : m ≠ 0)
    (s t : ℝ≥0) (x : E) :
    shiftedContinuation (linearGaussian L s) m
      (shiftedContinuation (linearGaussian L t) m F) x =
        shiftedContinuation (linearGaussian L (s+t)) m F x := by
  have hi := (exponentialIncrement_linearGaussian L (s+t)).integrable_shift hF m x
  have he := integral_linearGaussian_add L s t hi
  simp only [shiftedContinuation]
  congr 1
  congr 1
  rw [he]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    simpa only [add_assoc,shiftedContinuation] using exp_mul_shiftedContinuation hm (x+y)
      ((exponentialIncrement_linearGaussian L t).integrable_shift hF m (x+y))

 

theorem shiftedMean_linearGaussian_add (L : (ι → ℝ) →L[ℝ] E)
    {F A : E → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    {m : ℝ} (hm : m ≠ 0) (s t : ℝ≥0) (x : E) :
    shiftedMean (linearGaussian L s) m (shiftedContinuation (linearGaussian L t) m F)
      (shiftedMean (linearGaussian L t) m F A) x =
        shiftedMean (linearGaussian L (s+t)) m F A x := by
  have hi := (exponentialIncrement_linearGaussian L (s+t)).integrable_shift hF m x
  have hiA := hA.integrable_shifted_weighted hi
  have hd := integral_linearGaussian_add L s t hi
  have hn := integral_linearGaussian_add L s t hiA
  unfold shiftedMean tiltedMean
  congr 1
  · rw [hn]
    apply integral_congr_ae
    refine Eventually.of_forall fun y => ?_
    dsimp only
    have hi' := (exponentialIncrement_linearGaussian L t).integrable_shift hF m (x+y)
    rw [exp_mul_shiftedContinuation hm _ hi',div_mul_cancel₀ _ (partition_pos m hi').ne']
    simp only [add_assoc]
  · rw [hd]
    apply integral_congr_ae
    refine Eventually.of_forall fun y => ?_
    dsimp only
    rw [exp_mul_shiftedContinuation hm _
      ((exponentialIncrement_linearGaussian L t).integrable_shift hF m (x+y))]
    simp only [add_assoc]

end SKFluctuations.Hierarchy

end

end OAI
