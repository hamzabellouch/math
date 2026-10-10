import OAI.Analysis.CharacterCriterion.PrimeSquare

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.DiagonalIteration
open scoped CStarAlgebra ComplexOrder
open Filter Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
abbrev conj (v : unitary A) := Unitary.conjStarAlgAut ℂ A v
lemma conj_mul (u v : unitary A) (a : A) : conj (u*v) a=conj u (conj v a) := by
  simp [conj,Unitary.conjStarAlgAut_apply,mul_assoc]
lemma conj_one (a : A) : conj (1:unitary A) a=a := by simp [conj]
lemma conj_star (u : unitary A) (a : A) : conj (star u) (conj u a)=a := by
  simp only [conj,Unitary.conjStarAlgAut_apply,Unitary.coe_star,star_star]
  rw [←mul_assoc,←mul_assoc,u.property.1,one_mul,mul_assoc,u.property.1,mul_one]
lemma normalize_cancel (u v : unitary A) (a : A) :
    conj (star (u*star v)) (conj u a)=conj v a := by
  rw [star_mul,star_star,conj_mul,conj_star]

def piUnitary {ι : Type*} (v : ι → unitary A) : unitary (ι→A) :=
  ⟨fun i => v i,⟨by funext i; exact (v i).property.1,by funext i; exact (v i).property.2⟩⟩
lemma piUnitary_continuous {X ι : Type*} [TopologicalSpace X]
    (v : X → ι → unitary A) (hv : ∀ i, Continuous (fun x => v x i)) :
    Continuous (fun x => piUnitary (v x)) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => continuous_subtype_val.comp (hv i))
lemma mapUnitary_continuous (φ : A →⋆ₐ[ℂ] B) : Continuous (Unitary.map (StarMonoidHom.ofClass φ)) :=
  ((map_continuous φ).comp continuous_subtype_val).subtype_mk _
lemma map_pi_conj {ι : Type*} [Fintype ι] (φ : (ι→A) →⋆ₐ[ℂ] B)
    (v : ι→unitary A) (a : ι→A) : φ (fun i => conj (v i) (a i)) =
      conj (Unitary.map (StarMonoidHom.ofClass φ) (piUnitary v)) (φ a) := by
  change φ ((fun i => (v i:A))*a*star (fun i => (v i:A)))=
    φ (fun i => (v i:A))*φ a*star (φ (fun i => (v i:A)))
  rw [map_mul,map_mul,map_star]

structure System where
  obj : ℕ → Type*
  [cstar : ∀ n, CStarAlgebra (obj n)]
  slot : ℕ → Type*
  [finite : ∀ n, Fintype (slot n)]
  diagonal : ∀ n, (slot n → obj n) →⋆ₐ[ℂ] obj (n+1)
  eigen : ∀ n, slot n → C(unitInterval,unitInterval)
  twist : ∀ n, C(unitInterval,unitary (obj (n+1)))
attribute [instance] System.cstar System.finite
namespace System
variable (S : System)

def flat (n : ℕ) : (k : ℕ) → (unitInterval → S.obj n) → unitInterval → S.obj (n+k)
  | 0, f, t => f t
  | k+1, f, t => S.diagonal (n+k) (fun i => flat n k f (S.eigen (n+k) i t))
def full (n : ℕ) : (k : ℕ) → (unitInterval → S.obj n) → unitInterval → S.obj (n+k)
  | 0, f, t => f t
  | k+1, f, t => conj (S.twist (n+k) t)
      (S.diagonal (n+k) (fun i => full n k f (S.eigen (n+k) i t)))
def unitaryPath (n : ℕ) : (k : ℕ) → unitInterval → unitary (S.obj (n+k))
  | 0, _ => 1
  | k+1, t => S.twist (n+k) t * Unitary.map (StarMonoidHom.ofClass (S.diagonal (n+k)))
      (piUnitary (fun i => unitaryPath n k (S.eigen (n+k) i t)))

lemma full_eq (n k : ℕ) (f : unitInterval → S.obj n) (t : unitInterval) :
    S.full n k f t=conj (S.unitaryPath n k t) (S.flat n k f t) := by
  induction k generalizing t with
  | zero => exact (conj_one _).symm
  | succ k ih =>
    simp only [full,flat,unitaryPath,ih,map_pi_conj,conj_mul]
    rfl

lemma flat_continuous (n k : ℕ) (f : unitInterval → S.obj n) (hf : Continuous f) :
    Continuous (S.flat n k f) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    exact (map_continuous (S.diagonal (n+k))).comp
      (continuous_pi (fun i => ih.comp (S.eigen (n+k) i).continuous))
lemma unitaryPath_continuous (n k : ℕ) : Continuous (S.unitaryPath n k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    exact (S.twist (n+k)).continuous.mul ((mapUnitary_continuous _).comp
      (piUnitary_continuous _ (fun i => ih.comp (S.eigen (n+k) i).continuous)))

lemma flat_bound (hlip : ∀ n i, LipschitzWith (1/2) (S.eigen n i))
    (n k : ℕ) (f : unitInterval → S.obj n) (ε r : ℝ) (hε : 0≤ε)
    (hf : ∀ s t : unitInterval, dist s t ≤ (1/2:ℝ)^k*r → ‖f s-f t‖≤ε)
    (s t : unitInterval) (hst : dist s t≤r) :
    ‖S.flat n k f s-S.flat n k f t‖≤ε := by
  induction k generalizing r s t with
  | zero => exact hf s t (by simpa using hst)
  | succ k ih =>
    rw [flat,flat,←map_sub]
    apply (NonUnitalStarAlgHom.norm_apply_le (S.diagonal (n+k)) _).trans
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    apply ih (r/2)
    · intro x y hxy
      apply hf x y
      convert hxy using 1; ring
    · calc
        dist (S.eigen (n+k) i s) (S.eigen (n+k) i t) ≤
            (1/2:ℝ)*dist s t := (hlip (n+k) i).dist_le_mul s t
        _ ≤ r/2 := by linarith

lemma flat_eventually_small (hlip : ∀ n i, LipschitzWith (1/2) (S.eigen n i))
    (n : ℕ) (f : C(unitInterval,S.obj n)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k in atTop, ∀ s t : unitInterval, ‖S.flat n k f s-S.flat n k f t‖≤ε := by
  obtain ⟨δ,hδ,hf⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hp.eventually (gt_mem_nhds hδ)] with k hk s t
  apply S.flat_bound hlip n k f ε 1 hε.le
  · intro x y hxy
    apply le_of_lt
    rw [←dist_eq_norm]
    apply hf
    exact lt_of_le_of_lt (by simpa using hxy) hk
  · change |(s:ℝ)-(t:ℝ)|≤1
    exact abs_le.mpr ⟨by linarith [s.property.1,t.property.2],by linarith [s.property.2,t.property.1]⟩
end System
end KirchbergRordam.DiagonalIteration
namespace KirchbergRordam.BalancedDropIteration
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open BalancedDropMultiplicity BalancedDropSystem MatrixDiagonalPath DiagonalIteration

abbrev diagonalSystem : DiagonalIteration.System where
  obj n := PrimeDimensionDrop.Fiber (stage n) (stage n+1)
  slot n := Slot (stage n)
  diagonal n := (CStarMatrix.reindexₐ ℂ ℂ (zeroReindex (stage n) (stage_two n))).toStarAlgHom.comp block
  eigen n := eigenpath (stage n)
  twist n := (MatrixPermutationPath.path 1
    ((zeroReindex (stage n) (stage_two n)).symm.trans (oneReindex (stage n) (stage_two n)))).toContinuousMap

lemma eigen_lipschitz : ∀ n i, LipschitzWith (1/2) (diagonalSystem.eigen n i) := by
  intro n i
  rcases i with i|i|i
  · apply LipschitzWith.of_dist_le_mul
    intro s t
    change |(s:ℝ)/2-(t:ℝ)/2|≤(1/2:ℝ)*|(s:ℝ)-(t:ℝ)|
    rw [←sub_div,abs_div]
    norm_num
    linarith
  · apply LipschitzWith.of_dist_le_mul
    intro s t
    change |((s:ℝ)+1)/2-((t:ℝ)+1)/2|≤(1/2:ℝ)*|(s:ℝ)-(t:ℝ)|
    rw [←sub_div,add_sub_add_right_eq_sub,abs_div]
    norm_num
    linarith
  · exact (LipschitzWith.const _).weaken (by norm_num)

lemma iterate_full (n k : ℕ) (f : BalancedDropLimit.Stage n) (t : unitInterval) :
    (BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) f).val t =
      diagonalSystem.full n k f.val t := by
  induction k generalizing t with
  | zero => simp only [Nat.add_zero,BalancedDropLimit.chain.map_self,DiagonalIteration.System.full]; rfl
  | succ k ih =>
    erw [BalancedDropLimit.chain.map_succ n (n+k) (Nat.le_add_right n k)]
    change MatrixDiagonalPath.interpolate _ _ t
      (block (fun i => (BalancedDropLimit.chain.map n (n+k) _ f).val (eigenpath (stage (n+k)) i t))) = _
    simp only [ih]
    rfl

def normalizedPath (n k : ℕ) (t : unitInterval) :
    unitary (PrimeDimensionDrop.Fiber (stage (n+k)) (stage (n+k)+1)) :=
  diagonalSystem.unitaryPath n k t * star (diagonalSystem.unitaryPath n k 0)
lemma normalizedPath_continuous (n k : ℕ) : Continuous (normalizedPath n k) :=
  (diagonalSystem.unitaryPath_continuous n k).mul continuous_const
@[simp] lemma normalizedPath_zero (n k : ℕ) : normalizedPath n k 0=1 := by
  exact mul_inv_cancel _

lemma untwist (n k : ℕ) (f : BalancedDropLimit.Stage n) (t : unitInterval) :
    conj (star (normalizedPath n k t))
      ((BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) f).val t) =
      conj (diagonalSystem.unitaryPath n k 0) (diagonalSystem.flat n k f.val t) := by
  rw [iterate_full,diagonalSystem.full_eq]
  exact DiagonalIteration.normalize_cancel _ _ _

lemma untwist_norm (n k : ℕ) (f : BalancedDropLimit.Stage n) (t : unitInterval) :
    ‖conj (star (normalizedPath n k t))
      ((BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
      (BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖ =
      ‖diagonalSystem.flat n k f.val t-diagonalSystem.flat n k f.val 0‖ := by
  rw [untwist,iterate_full,diagonalSystem.full_eq]
  rw [←map_sub,StarAlgEquiv.norm_map]

lemma eventually_untwist_small (n : ℕ) (f : BalancedDropLimit.Stage n) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k in atTop, ∀ t : unitInterval,
      ‖conj (star (normalizedPath n k t))
        ((BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
        (BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖≤ε := by
  filter_upwards [diagonalSystem.flat_eventually_small eigen_lipschitz n f.val ε hε] with k hk t
  rw [untwist_norm]
  exact hk t 0
end KirchbergRordam.BalancedDropIteration


namespace KirchbergRordam.FiniteHalfFlipSequence
open scoped CStarAlgebra ComplexOrder
open Filter Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
abbrev conj (u : unitary B) := Unitary.conjStarAlgAut ℂ B u

lemma perturbation (φ ψ : A →⋆ₐ[ℂ] B) (u : unitary B) (x y : A) :
    ‖conj u (φ x)-ψ x‖ ≤ 2*‖x-y‖+‖conj u (φ y)-ψ y‖ := by
  have he : conj u (φ x)-ψ x =
      conj u (φ (x-y))+(conj u (φ y)-ψ y)-ψ (x-y) := by
    rw [map_sub,map_sub,map_sub]
    abel
  rw [he]
  have h1 : ‖conj u (φ (x-y))‖≤‖x-y‖ := by
    rw [StarAlgEquiv.norm_map]
    exact NonUnitalStarAlgHom.norm_apply_le φ _
  have h2 : ‖ψ (x-y)‖≤‖x-y‖ := NonUnitalStarAlgHom.norm_apply_le ψ _
  have h3 := norm_sub_le (conj u (φ (x-y))+(conj u (φ y)-ψ y)) (ψ (x-y))
  have h4 := norm_add_le (conj u (φ (x-y))) (conj u (φ y)-ψ y)
  linarith

theorem exists_sequence [TopologicalSpace.SeparableSpace A]
    (φ ψ : A →⋆ₐ[ℂ] B)
    (h : ∀ F : Finset A, ∀ ε : ℝ, 0<ε → ∃ u : unitary B,
      ∀ x∈F, ‖conj u (φ x)-ψ x‖≤ε) :
    ∃ u : ℕ → unitary B, ∀ x : A,
      Tendsto (fun n => conj (u n) (φ x)) atTop (𝓝 (ψ x)) := by
  classical
  let a := TopologicalSpace.denseSeq A
  have he (n : ℕ) : 0<(1:ℝ)/((n:ℝ)+1) := by positivity
  choose u hu using fun n : ℕ => h ((Finset.range (n+1)).image a) (1/((n:ℝ)+1)) (he n)
  refine ⟨u,fun x => ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨i,hi⟩ := (TopologicalSpace.denseRange_denseSeq A).exists_dist_lt x (by positivity : 0<ε/4)
  have hp : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hp.eventually (gt_mem_nhds (by positivity : 0<ε/2)))
  refine ⟨max i N,fun n hn => ?_⟩
  have hin : i∈Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_max_left i N).trans hn))
  have hb := hu n (a i) (Finset.mem_image_of_mem a hin)
  have hp' := perturbation φ ψ (u n) x (a i)
  rw [dist_eq_norm] at hi ⊢
  have hn' := hN n ((le_max_right i N).trans hn)
  have hx : ‖x-a i‖<ε/4 := by simpa only [a,norm_sub_rev] using hi
  linarith
end KirchbergRordam.FiniteHalfFlipSequence
namespace KirchbergRordam.CStarInductiveLimit
lemma approximation_common_stage (S : System) (F : Finset (Algebra S)) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ, ∃ a : Algebra S → S.obj n, ∀ x∈F, ‖of S n (a x)-x‖<ε := by
  classical
  choose v hv using fun x : Algebra S => (denseRange_of S).exists_dist_lt x hε
  let n := F.sup (fun x => (v x).1)
  let a : Algebra S → S.obj n := fun x => if hx : x∈F then
    S.map (v x).1 n (Finset.le_sup (f:=fun x => (v x).1) hx) (v x).2 else 0
  refine ⟨n,a,fun x hx => ?_⟩
  dsimp only [a]
  rw [dite_eq_left hx,of_map]
  simpa only [dist_eq_norm,norm_sub_rev] using hv x
end KirchbergRordam.CStarInductiveLimit
namespace KirchbergRordam.BalancedDropHalfFlip
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open BalancedDropLimit BalancedDropIteration
open UnitaryDisplacement
universe u

variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
def squareMap (φ : A →⋆ₐ[ℂ] B) : MaxTensor.Algebra A A →⋆ₐ[ℂ] MaxTensor.Algebra B B :=
  MaxTensor.lift (MaxTensor.includeLeft.comp φ) (MaxTensor.includeRight.comp φ)
    (fun a b => MaxTensor.legs_commute (φ a) (φ b))
lemma squareMap_left (φ : A →⋆ₐ[ℂ] B) (a : A) :
    squareMap φ (MaxTensor.includeLeft a)=MaxTensor.includeLeft (φ a) := by
  exact DFunLike.congr_fun (MaxTensor.lift_includeLeft _ _ _) a
lemma squareMap_right (φ : A →⋆ₐ[ℂ] B) (a : A) :
    squareMap φ (MaxTensor.includeRight a)=MaxTensor.includeRight (φ a) := by
  exact DFunLike.congr_fun (MaxTensor.lift_includeRight _ _ _) a

lemma control_map (φ : A →⋆ₐ[ℂ] B) (w : unitary (MaxTensor.Algebra A A)) (a : A) :
    ‖conj (Unitary.map (StarMonoidHom.ofClass (squareMap φ)) w)
        (MaxTensor.includeLeft (φ a))-MaxTensor.includeRight (φ a)‖≤
      ‖conj w (MaxTensor.includeLeft a)-MaxTensor.includeRight a‖ := by
  rw [←squareMap_left,←squareMap_right,PrimeSquareUnitary.conj_map,←map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le (squareMap φ) _

lemma finite_stage (n : ℕ) (F : Finset (Stage n)) (ε : ℝ) (hε : 0<ε) :
    ∃ w : unitary (MaxTensor.Algebra Algebra Algebra), ∀ f∈F,
      ‖conj w (MaxTensor.includeLeft (inclusion n f))-
        MaxTensor.includeRight (inclusion n f)‖≤ε := by
  have he : ∀ᶠ k in atTop, ∀ f∈F, ∀ t : unitInterval,
      ‖conj (star (normalizedPath n k t))
        ((chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
        (chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖≤ε/4 := by
    apply (Filter.eventually_all_finset F).mpr
    intro f hf
    exact eventually_untwist_small n f (ε/4) (by positivity)
  obtain ⟨k,hk⟩ := he.exists
  obtain ⟨w,hw⟩ := PrimeSquareUnitary.exists_half_flip_control (normalizedPath n k)
    (normalizedPath_continuous n k) (normalizedPath_zero n k)
  refine ⟨Unitary.map (StarMonoidHom.ofClass (squareMap (inclusion (n+k)))) w,fun f hf => ?_⟩
  have hc := (control_map (inclusion (n+k)) w (chain.map n (n+k) (Nat.le_add_right n k) f)).trans
    (hw _ (ε/4) (hk f hf))
  have hm : inclusion (n+k) (chain.map n (n+k) (Nat.le_add_right n k) f)=inclusion n f :=
    CStarInductiveLimit.of_map system n (n+k) (Nat.le_add_right n k) f
  rw [hm] at hc
  have he : 4*(ε/4)=ε := by ring
  rwa [he] at hc

lemma common_stage (F : Finset Algebra) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ, ∃ a : Algebra → Stage n, ∀ x∈F, ‖inclusion n (a x)-x‖<ε :=
  CStarInductiveLimit.approximation_common_stage system F ε hε

lemma finite_control (F : Finset Algebra) (ε : ℝ) (hε : 0<ε) :
    ∃ w : unitary (MaxTensor.Algebra Algebra Algebra), ∀ x∈F,
      ‖conj w (MaxTensor.includeLeft x)-MaxTensor.includeRight x‖≤ε := by
  classical
  obtain ⟨n,a,ha⟩ := common_stage F (ε/4) (by positivity)
  obtain ⟨w,hw⟩ := finite_stage n (F.image a) (ε/2) (by positivity)
  refine ⟨w,fun x hx => ?_⟩
  have hb := hw (a x) (Finset.mem_image_of_mem a hx)
  have hc := FiniteHalfFlipSequence.perturbation MaxTensor.includeLeft MaxTensor.includeRight w x (inclusion n (a x))
  have hd := ha x hx
  rw [norm_sub_rev] at hd
  change ‖conj w (MaxTensor.includeLeft x)-MaxTensor.includeRight x‖≤
    2*‖x-inclusion n (a x)‖+‖conj w (MaxTensor.includeLeft (inclusion n (a x)))-MaxTensor.includeRight (inclusion n (a x))‖ at hc
  linarith


theorem exists_half_flip : ∃ w : ℕ → unitary (MaxTensor.Algebra Algebra Algebra),
    ∀ x : Algebra, Tendsto (fun n => conj (w n) (MaxTensor.includeLeft x)) atTop
      (𝓝 (MaxTensor.includeRight x)) :=
  FiniteHalfFlipSequence.exists_sequence MaxTensor.includeLeft MaxTensor.includeRight finite_control
end KirchbergRordam.BalancedDropHalfFlip
end

end OAI
