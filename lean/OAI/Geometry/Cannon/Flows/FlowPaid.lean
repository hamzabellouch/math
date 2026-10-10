import Mathlib
import OAI.Geometry.Cannon.CirclePacking.SplitRadiusRatioTendsto

namespace OAI

section
section
section
noncomputable section
section
namespace CannonApprox

open Set Metric Filter Topology MeasureTheory CannonNode CannonMagnification CannonPairs CannonPacking Finset

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

def FlowPaid {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (gi : ∀ g, Fin (F.S.flow.size g) → Γ)
    (c Cs Ci d : ℝ) (g : ℕ) (i j : Fin (F.S.flow.size g)) : Prop :=
  ∃ B : Set X, MeasurableSet B ∧ c*(F.S.len g i)^2 ≤ (T.ν B:ℝ) ∧
    B ⊆ closedBall (F.S.center g i) (Cs*F.S.scale g/d) ∧
    action (gi g i) '' B ⊆ closedBall (action (gi g j) T.z₀) (Ci*F.S.scale g)

omit [CompactSpace X] [BorelSpace X] in
theorem FlowSetup.no_pair_data {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hell : 0 < ell) (hQ : 0 < Q)
    (hB : 0 ≤ F.B+1) (hH : 4*(F.B+1) < F.H)
    (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X:=X) Q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (gi : ∀ g, Fin (F.S.flow.size g) → Γ)
    (P : FlowPatternSetup T F (fun g i => action (gi g i)))
    (c Cs Ci τ : ℝ) (hc : 0 < c) (hCs : 0 < Cs) (hτ : 0 < τ)
    (hHCs : F.H ≤ Cs) (hCsτ : Cs*τ ≤ 1)
    (N M : ℕ)
    (hmulti : ∀ g b, ((univ : Finset (Fin (F.S.flow.size g))).filter
      (fun i => dist (action (gi g i) T.z₀) b ≤ Ci*F.S.scale g)).card ≤ M)
    (hnear : ∀ g b, ∑ i ∈ (univ : Finset (Fin (F.S.flow.size g))).filter
      (fun i => dist (action (gi g i) T.z₀) b ≤ radius ell (160*(Q+1)*F.n*(g/(160*Q*(Q+1))))),
      F.S.flow.weight g i ≤ (N:ℝ)*Real.exp (-ell*F.n)^(g/(160*Q*(Q+1))))
    (hcost : ∀ g i j, F.S.good (F.S.state g i) → F.S.good (F.S.state g j) → P.pat g i=P.pat g j →
      ∀ d : ℝ, 0 < d → d ≤ 1 → F.S.scale g/d ≤ τ →
      d < dist (action (gi g i) T.z₀) (action (gi g j) T.z₀) →
        FlowPaid F gi c Cs Ci d g i j ∨ FlowPaid F gi c Cs Ci d g j i) : False := by
  classical
  have hHpos : 0 < F.H := by linarith only [hB,hH]
  let _ : Nonempty P.net := ⟨⟨P.net_nonempty.choose,P.net_nonempty.choose_spec⟩⟩
  obtain ⟨J,hJ⟩ := F.pattern_class hell.le hB hH CP hCP hpack hdiam P
  let K : ℝ := 6*(Fintype.card (Bool → P.net):ℝ)
  have hK : 0 < K := mul_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)
  let D := 160*(Q+1)*F.n
  let q := 160*Q*(Q+1)
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : 0 < 2) (pair_split_ratio Q hQ)
  let kval (g : ℕ) : ℝ := K*((J:ℝ)*(F.S.kmin+(D:ℝ)*g)+1)
  have hkval (g : ℕ) : 0 < kval g := mul_pos hK (by dsimp only [D]; positivity)
  have hsmall : ∀ᶠ g : ℕ in atTop,
      F.S.scale g/radius ell (D*(g/q)) ≤ τ :=
    (split_radius_ratio_tendsto Q F.n F.S.kmin hQ F.npos hell).eventually (eventually_le_nhds hτ)
  have hnearSmall : ∀ᶠ g : ℕ in atTop,
      2*(N:ℝ)*Real.exp (-ell*F.n)^(g/q) ≤ 1/kval g :=
    eventually_near_class_threshold hq hell F.n F.npos (N:ℝ) K J F.S.kmin D hK
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  let C := (2*CP*(Cs/F.H)^Q*M*(T.ν univ:ℝ))/(c*F.S.root.length^2/2)
  have hfreq : ∃ᶠ g : ℕ in atTop, (1/2:ℝ) ≤ F.S.flow.goodMass g :=
    frequently_atTop.mpr F.good
  apply CannonPairCost.not_frequently_exp_le_quadratic
    (mul_pos hell (Nat.cast_pos.mpr F.npos)) C (K*((J:ℝ)*F.S.kmin+1)) (K*J*D)
  apply (hfreq.and_eventually (hJ.and (hsmall.and hnearSmall))).mono
  intro g hg
  obtain ⟨S,v,pstar,hpstar,hclass,hsize⟩ := hg.2.1 hg.1
  have hsize' : 1/kval g ≤ (S.card:ℝ)*pstar := by
    convert hsize using 1
    dsimp only [kval,K,D]
    push_cast
    ring
  let d := radius ell (D*(g/q))
  have hd : 0 < d := radius_pos _ _
  have hd1 : d ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hell.le) (Nat.cast_nonneg _))
  let near (i j : Fin (F.S.flow.size g)) : Prop :=
    dist (action (gi g j) T.z₀) (action (gi g i) T.z₀) ≤ d
  let pairs := (S ×ˢ S).filter (fun ij => ¬ near ij.1 ij.2)
  have hfar : (S.card:ℝ)^2/2 ≤ (pairs.card:ℝ) := by
    apply far_pairs_card S (F.S.flow.weight g) near pstar
      ((N:ℝ)*Real.exp (-ell*F.n)^(g/q)) hpstar (fun i hi => (hclass i hi).2.2.1)
    · intro i _
      apply le_trans ?_ (hnear g (action (gi g i) T.z₀))
      apply sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => F.S.flow.nonneg g j)
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩
    · have hh := hg.2.2.2.trans hsize'
      nlinarith only [hh]
  have hP : pairs ⊆ S ×ˢ S := filter_subset _ _
  have hswap : ∀ ij ∈ pairs, ij.swap ∈ pairs := by
    intro ij hij
    obtain ⟨hm,hn⟩ := mem_filter.mp hij
    obtain ⟨hi,hj⟩ := mem_product.mp hm
    apply mem_filter.mpr ⟨mem_product.mpr ⟨hj,hi⟩,?_⟩
    simpa only [near,Prod.fst_swap,Prod.snd_swap,dist_comm] using hn
  have hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → F.H*F.S.scale g ≤
      dist (F.S.center g i) (F.S.center g j) :=
    fun i _ j _ hij => F.S.centers_separated F.decay hB hH g i j hij
  have hmultS (b : X) : (S.filter (fun j => dist (action (gi g j) T.z₀) b ≤ Ci*F.S.scale g)).card ≤ M :=
    (Finset.card_le_card (filter_subset_filter _ (subset_univ S))).trans (hmulti g b)
  have hpaid (ij : Fin (F.S.flow.size g) × Fin (F.S.flow.size g)) (hij : ij ∈ pairs) :
      FlowPaid F gi c Cs Ci d g ij.1 ij.2 ∨ FlowPaid F gi c Cs Ci d g ij.2 ij.1 := by
    obtain ⟨hm,hn⟩ := mem_filter.mp hij
    obtain ⟨hi,hj⟩ := mem_product.mp hm
    apply hcost g ij.1 ij.2 (hclass _ hi).1 (hclass _ hj).1
      ((hclass _ hi).2.1.trans (hclass _ hj).2.1.symm) d hd hd1 hg.2.2.1
    simpa only [near,not_le,dist_comm] using hn
  have hgap (i : Fin (F.S.flow.size g)) (_hi : i ∈ S) :
      (F.S.root.length*Real.exp (ell*F.n*g))*F.S.flow.weight g i ≤ F.S.len g i := by
    have heq : Real.exp (ell*F.n*g)*(Real.exp (-ell*F.n))^g=1 := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      convert Real.exp_zero using 1
      congr 1
      ring
    calc _ = Real.exp (ell*F.n*g)*(F.S.root.length*F.S.flow.weight g i) := by ring
         _ ≤ Real.exp (ell*F.n*g)*((Real.exp (-ell*F.n))^g*F.S.len g i) :=
           mul_le_mul_of_nonneg_left (F.S.weight_linear g i) (Real.exp_pos _).le
         _ = _ := by rw [← mul_assoc,heq,one_mul]
  have hscaleSmall : Cs*F.S.scale g/d ≤ 1 := by
    calc _ = Cs*(F.S.scale g/d) := by ring
         _ ≤ Cs*τ := mul_le_mul_of_nonneg_left hg.2.2.1 hCs.le
         _ ≤ 1 := hCsτ
  have hcomparison := charged_pair_comparison T.ν Q CP F.H (F.S.scale g) d Cs Ci hpack
    hHpos (radius_pos _ _) hd hHCs hd1 hscaleSmall S pairs (F.S.center g)
    (fun i => action (gi g i) T.z₀) (fun i => action (gi g i)) M hP hswap hsep hmultS
    (F.S.len g) (F.S.flow.weight g) c (F.S.root.length*Real.exp (ell*F.n*g)) pstar (kval g)
    hc.le (mul_pos F.S.root.length_pos (Real.exp_pos _)).le hpstar.le (hkval g)
    (fun i hi => (hclass i hi).2.2.1) hgap (fun ij => FlowPaid F gi c Cs Ci d g ij.1 ij.2)
    hpaid (fun _ _ hh => hh) hfar hsize'
  have hbound := pair_cost_exponential_bound Q F.n g hQ hell.le hc F.S.root.length_pos
    hCP hCs.le hHpos (by positivity : 0 ≤ (T.ν univ:ℝ)) M hcomparison
  convert hbound using 1
  · dsimp only [C,kval]
    congr 2
    ring

end CannonApprox

end

section
section

section

section

section

section

section

section

section

section

section

section

section

namespace CannonCapacity

open Finset Set

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

open Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

open Set Metric Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification

attribute [local instance] Classical.propDecidable

end CannonNode

end

section

section

open Set Filter Finset

namespace CannonFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

end CannonFlow

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

end CannonFlow

end

namespace CannonNode

open Set Metric Finset CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

end

section

open Set Filter Finset

namespace CannonFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

end CannonFlow

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

end CannonFlow

end

section

open Set Finset MeasureTheory Filter

namespace CannonPairCost

attribute [local instance] Classical.propDecidable

end CannonPairCost

end

namespace CannonNode.SourceConstruction

open Set Metric Finset Filter Topology CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end CannonNode.SourceConstruction

namespace CannonNode.SourceConstruction

open Set Metric Finset MeasureTheory CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end CannonNode.SourceConstruction

end

namespace CannonNode

open Set Metric CannonCapacity CannonMagnification

namespace SourceConstruction

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] [ProperSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end SourceConstruction

end CannonNode

end

end

end

section

section

section

section

section

section

section

section

section

namespace CannonCapacity

open Finset Set

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

open Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

open Set Metric Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification

attribute [local instance] Classical.propDecidable

end CannonNode

end

section

section

open Set Filter Finset

namespace CannonFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

end CannonFlow

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

end CannonFlow

end

namespace CannonNode

open Set Metric Finset CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

end

section

open Set Filter Finset

namespace CannonFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

end CannonFlow

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

end CannonFlow

end

section

open Set Finset MeasureTheory Filter

namespace CannonPairCost

attribute [local instance] Classical.propDecidable

end CannonPairCost

end

namespace CannonNode.SourceConstruction

open Set Metric Finset Filter Topology CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end CannonNode.SourceConstruction

namespace CannonNode.SourceConstruction

open Set Metric Finset MeasureTheory CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end CannonNode.SourceConstruction

end

namespace CannonNode

open Set Metric CannonCapacity CannonMagnification

namespace SourceConstruction

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] [ProperSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end SourceConstruction

end CannonNode

end

end
end
end
end
end
end

end OAI
