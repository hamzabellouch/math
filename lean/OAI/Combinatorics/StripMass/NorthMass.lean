import Mathlib
import OAI.Combinatorics.StripMass.NorthBijection

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram

lemma sum_subtype_indicator {α : Type*} [Fintype α] (P : α→Prop) (f : α→ℝ) :
    (∑ x : {a // P a},f x.val)=∑ x,if P x then f x else 0 := by
  rw [←Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp) f).symm

namespace NorthHistory
variable {N m : ℕ}

def Valid (l r : Fin m → Configuration (N+1)) : Prop :=
  ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn l)≠0 ∧
  ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn r)≠0 ∧
  ∃p q : Pairing (N+1), ColumnChain.Runs (empty (N+1)) (List.ofFn l) p ∧
    ColumnChain.Runs (empty (N+1)) (List.ofFn r) q ∧ p.GluesAt (Fin.last N) q

def pairEquiv : NorthHistory N m ≃
    {lr : (Fin m → Configuration (N+1)) × (Fin m → Configuration (N+1)) // Valid lr.1 lr.2} where
  toFun h := ⟨(h.left,h.right),h.nzleft,h.nzright,h.realizes⟩
  invFun h := ⟨h.val.1,h.val.2,h.property.1,h.property.2.1,h.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma weighted_valid (l r : Fin m → Configuration (N+1)) :
    (if Valid l r then ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn l)*
        ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn r) else 0)=
      ∑p : Pairing (N+1),∑q : Pairing (N+1),
        (if ColumnChain.Runs (empty (N+1)) (List.ofFn l) p then
          ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn l) else 0)*
        (if p.GluesAt (Fin.last N) q then (1:ℝ) else 0)*
        (if ColumnChain.Runs (empty (N+1)) (List.ofFn r) q then
          ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn r) else 0) := by
  by_cases hl : ∃p,ColumnChain.Runs (empty (N+1)) (List.ofFn l) p
  · obtain ⟨p,hp⟩:=hl
    have hpl (x : Pairing (N+1)) :
        ColumnChain.Runs (empty (N+1)) (List.ofFn l) x ↔ x=p :=
      ⟨fun h=>ColumnChain.runs_unique h hp,fun h=>h ▸ hp⟩
    by_cases hr : ∃q,ColumnChain.Runs (empty (N+1)) (List.ofFn r) q
    · obtain ⟨q,hq⟩:=hr
      have hqr (x : Pairing (N+1)) :
          ColumnChain.Runs (empty (N+1)) (List.ofFn r) x ↔ x=q :=
        ⟨fun h=>ColumnChain.runs_unique h hq,fun h=>h ▸ hq⟩
      rw [Finset.sum_eq_single p]
      · rw [Finset.sum_eq_single q]
        · by_cases hwl : ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn l)=0
          · simp [Valid,hpl,hqr,hwl]
          · by_cases hwr : ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn r)=0
            · simp [Valid,hpl,hqr,hwr]
            · simp only [Valid,hpl,hqr,hwl,hwr,ne_eq,not_false_eq_true,true_and,
                ite_true]
              have he : (∃ p₁ q₁ : Pairing (N+1), p₁=p ∧ q₁=q ∧ p₁.GluesAt (Fin.last N) q₁) ↔
                  p.GluesAt (Fin.last N) q :=
                ⟨by rintro ⟨_,_,rfl,rfl,h⟩; exact h, fun h=>⟨p,q,rfl,rfl,h⟩⟩
              simp only [he]
              split_ifs <;> simp
        · intro q' _ hq'
          simp only [hqr,hq',ite_false,mul_zero]
        · simp
      · intro p' _ hp'
        simp only [hpl,hp',ite_false,zero_mul,Finset.sum_const_zero]
      · simp
    · have he (q : Pairing (N+1)) : ¬ColumnChain.Runs (empty (N+1)) (List.ofFn r) q :=
        fun h=>hr ⟨q,h⟩
      simp only [Valid,he,false_and,and_false,exists_false,ite_false,mul_zero,Finset.sum_const_zero]
  · have he (p : Pairing (N+1)) : ¬ColumnChain.Runs (empty (N+1)) (List.ofFn l) p :=
      fun h=>hl ⟨p,h⟩
    simp only [Valid,he,false_and,exists_false,and_false,ite_false,zero_mul,Finset.sum_const_zero]

lemma sum_weight_pairings (N m : ℕ) :
    (∑ h : NorthHistory N m,h.weight)=
      ∑p : Pairing (N+1),∑q : Pairing (N+1),
        (column (SewnRectangle.leftWeights N)^m) p (empty (N+1))*
        (if p.GluesAt (Fin.last N) q then (1:ℝ) else 0)*
        (column (SewnRectangle.rightWeights N)^m) q (empty (N+1)) := by
  rw [show (∑h : NorthHistory N m,h.weight)=
      ∑ h : {lr : (Fin m → Configuration (N+1)) × (Fin m → Configuration (N+1)) // Valid lr.1 lr.2},
        ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn h.val.1)*
        ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn h.val.2) from
    Fintype.sum_equiv pairEquiv _ _ (fun _=>rfl)]
  rw [sum_subtype_indicator (fun lr : (Fin m → Configuration (N+1)) × (Fin m → Configuration (N+1))=>Valid lr.1 lr.2)
    (fun lr=>ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn lr.1)*
      ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn lr.2)),Fintype.sum_prod_type]
  simp_rw [weighted_valid]
  simp_rw [←ColumnChain.mass_eq_pow,ColumnChain.mass,Finset.sum_mul,Finset.mul_sum]
  conv_lhs => arg 2; intro l; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  conv_lhs => arg 2; intro l; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

lemma sum_weight_source (N m : ℕ) :
    (∑ h : NorthHistory N m,h.weight)=
      sourceGlue N (fun p=>(column (SewnRectangle.leftWeights N)^m) p.val (empty (N+1)))
        (fun q=>(column (SewnRectangle.rightWeights N)^m) q.val (empty (N+1))) := by
  rw [sum_weight_pairings,←(sourceFullSplit N).sum_comp,sourceGlue_eq_sum]
  simp_rw [←(sourceFullSplit N).sum_comp]
  have hl (p : Pairing N) (q : Pairing (N+1)) : ¬p.padTop.GluesAt (Fin.last N) q :=
    fun h=>Pairing.padTop_not_occupied_last p h.1
  have hr (p : Pairing (N+1)) (q : Pairing N) : ¬p.GluesAt (Fin.last N) q.padTop :=
    fun h=>Pairing.padTop_not_occupied_last q ((h.2.1 _).mp h.1)
  simp only [Fintype.sum_sum_type,sourceFullSplit_inl,sourceFullSplit_inr,hl,hr,ite_false,mul_zero,
    zero_mul,Finset.sum_const_zero,zero_add,mul_assoc]
  rfl

instance boundedFintype (N m : ℕ) [hN : Fact (1≤N)] : Fintype (CrossTopArch.Bounded N m) :=
  Fintype.ofEquiv (NorthHistory N m) (equivCross hN.out)

lemma sum_weight_cross (N m : ℕ) (hN : 1≤N) [Fintype (CrossTopArch.Bounded N m)] :
    (∑ h : NorthHistory N m,h.weight)=∑D : CrossTopArch.Bounded N m,D.val.weight :=
  Fintype.sum_equiv (equivCross hN) _ _ (fun h=>toCross_weight h hN)

end NorthHistory
end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators
open _root_.Matrix _root_.OAI.Matrix Filter Topology

lemma column_pow_empty_empty {n : ℕ} (w : Fin n → Weights ℝ) (m : ℕ) :
    (column w^m) (empty n) (empty n)=1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    change (column w).mulVec (fun p=>(column w^m) p (empty n)) (empty n)=1
    rw [column_mulVec_empty,ih]

 

lemma column_pow_empty_nonempty {n : ℕ} (w : Fin n → Weights ℝ)
    (v : NonemptyPairing n → ℝ)
    (hv : (restrictedColumn w).mulVec v+injectionColumn w=v) (m : ℕ) :
    ∀ p : NonemptyPairing n, (column w^m) p.val (empty n)=
      v p-(restrictedColumn w^m).mulVec v p := by
  induction m with
  | zero =>
    intro p
    simp only [pow_zero,Matrix.one_apply,p.property,ite_false,Matrix.one_mulVec,sub_self]
  | succ m ih =>
    intro p
    rw [pow_succ']
    change (column w).mulVec (fun q=>(column w^m) q (empty n)) p.val=_
    rw [column_mulVec_nonempty,column_pow_empty_empty,mul_one]
    have he : (fun q : NonemptyPairing n=>(column w^m) q.val (empty n))=
        v-(restrictedColumn w^m).mulVec v := funext ih
    rw [he,Matrix.mulVec_sub,Matrix.mulVec_mulVec,←pow_succ']
    have hp:=congrFun hv p
    simp only [Pi.add_apply] at hp
    simp only [Pi.sub_apply]
    linarith

theorem column_pow_empty_tendsto {n : ℕ} (w : Fin n → Weights ℝ)
    (hs : PositiveMatrix.SummablePowers (restrictedColumn w))
    (v : NonemptyPairing n → ℝ)
    (hv : (restrictedColumn w).mulVec v+injectionColumn w=v) (p : NonemptyPairing n) :
    Tendsto (fun m : ℕ=>(column w^m) p.val (empty n)) atTop (𝓝 (v p)) := by
  simp_rw [column_pow_empty_nonempty w v hv]
  have hh:=(hs.mulVec_tendsto_zero v p).const_sub (v p)
  simpa only [sub_zero] using hh

lemma physical_augmented_stationary (N : ℕ) :
    (restrictedColumn (SewnRectangle.leftWeights N)).mulVec
        (fun p=>angleAugmented (fun _ : Fin N=>lambda) p.val)+
      injectionColumn (SewnRectangle.leftWeights N)=
      fun p=>angleAugmented (fun _ : Fin N=>lambda) p.val := by
  simpa only [show 3*lambda-lambda=2*lambda by ring,SewnRectangle.leftWeights] using
    angleAugmented_restricted_stationary (fun _ : Fin N=>lambda)
      (fun _=>homogeneous_L_ne_zero) (homogeneous_angleScalar_ne_zero N)

lemma reversed_augmented_stationary (N : ℕ) :
    (restrictedColumn (SewnRectangle.rightWeights N)).mulVec
        (fun p=>angleAugmented (fun _ : Fin N=>2*lambda) p.val)+
      injectionColumn (SewnRectangle.rightWeights N)=
      fun p=>angleAugmented (fun _ : Fin N=>2*lambda) p.val := by
  simpa only [show 3*lambda-2*lambda=lambda by ring,SewnRectangle.rightWeights] using
    angleAugmented_restricted_stationary (fun _ : Fin N=>2*lambda)
      (fun _=>reversed_L_ne_zero) (reversed_angleScalar_ne_zero N)

lemma physical_empty_tendsto_source (N : ℕ) (p : SourcePairing N) :
    Tendsto (fun m : ℕ=>(column (SewnRectangle.leftWeights N)^m) p.val (empty (N+1))) atTop
      (𝓝 (angleNorthSource (fun _ : Fin N=>lambda) p)) := by
  have hp : p.val≠empty (N+1) := by
    intro h; exact empty_not_occupied _ (h ▸ p.property)
  have hh:=column_pow_empty_tendsto (SewnRectangle.leftWeights N)
    (augmentedPhysical_summablePowers N) _ (physical_augmented_stationary N) ⟨p.val,hp⟩
  simpa only [angleAugmented,augmentVector_source] using hh

lemma reversed_empty_tendsto_source (N : ℕ) (p : SourcePairing N) :
    Tendsto (fun m : ℕ=>(column (SewnRectangle.rightWeights N)^m) p.val (empty (N+1))) atTop
      (𝓝 (angleNorthSource (fun _ : Fin N=>2*lambda) p)) := by
  have hp : p.val≠empty (N+1) := by
    intro h; exact empty_not_occupied _ (h ▸ p.property)
  have hh:=column_pow_empty_tendsto (SewnRectangle.rightWeights N)
    (augmentedReversed_summablePowers N) _ (reversed_augmented_stationary N) ⟨p.val,hp⟩
  simpa only [angleAugmented,augmentVector_source] using hh

end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical
open Diagram Filter Topology

namespace NorthHistory

lemma mass_tendsto (N : ℕ) :
    Tendsto (fun m : ℕ=>∑ h : NorthHistory N m,h.weight) atTop (𝓝 (realNorthSeparator N)) := by
  simp_rw [sum_weight_source]
  rw [realNorthSeparator,sourceGlue_symmetric]
  simp_rw [sourceGlue_eq_sum]
  apply tendsto_finsetSum
  intro p _
  apply tendsto_finsetSum
  intro q _
  exact (physical_empty_tendsto_source N p).mul
    ((reversed_empty_tendsto_source N q).const_mul _)

end NorthHistory

namespace CrossTopArch
variable {N : ℕ}

lemma weight_nonneg (D : CrossTopArch N) (hN : 1≤N) : 0≤D.weight := by
  rw [weight,←D.arch.weight_toArch hN,(D.arch.toArch hN).weight_eq_path hN (by
    intro he
    have hx:=BoundaryPort.bottom.inj he
    omega)]
  exact (pow_pos rho_pos _).le

lemma Fits.mono {D : CrossTopArch N} {m l : ℕ} (h : D.Fits m) (hm : m≤l) : D.Fits l :=
  HoneycombAssignment.Fits.mono h hm

def window (N m : ℕ) [Fact (1≤N)] : Finset (CrossTopArch N) :=
  (Finset.univ : Finset (Bounded N m)).map ⟨Subtype.val,Subtype.val_injective⟩

@[simp] lemma mem_window [Fact (1≤N)] (D : CrossTopArch N) (m : ℕ) :
    D∈window N m ↔ D.Fits m := by
  simp only [window,Finset.mem_map,Finset.mem_univ,true_and,Function.Embedding.coeFn_mk]
  exact ⟨fun ⟨D',he⟩=>he ▸ D'.property,fun h=>⟨⟨D,h⟩,rfl⟩⟩

lemma window_tendsto (N : ℕ) [hN : Fact (1≤N)] :
    Tendsto (fun m : ℕ=>window N m) atTop atTop := by
  apply tendsto_atTop.mpr
  intro F
  let b : CrossTopArch N → ℕ := fun D=>Classical.choose (D.exists_fits hN.out)
  have hb (D : CrossTopArch N) : D.Fits (b D) := Classical.choose_spec (D.exists_fits hN.out)
  apply eventually_atTop.mpr
  refine ⟨F.sup b,?_⟩
  intro m hm D hD
  rw [mem_window]
  exact (hb D).mono ((Finset.le_sup hD).trans hm)

lemma window_mass (N m : ℕ) [hN : Fact (1≤N)] :
    (∑D∈window N m,D.weight)=∑h : NorthHistory N m,h.weight := by
  rw [window,Finset.sum_map,NorthHistory.sum_weight_cross N m hN.out]
  rfl

 

theorem summable_weight (N : ℕ) (hN : 1≤N) : Summable (weight (N:=N)) := by
  let : Fact (1≤N) := ⟨hN⟩
  have hlim : Tendsto (fun m : ℕ=>∑D∈window N m,D.weight) atTop (𝓝 (realNorthSeparator N)) := by
    simpa only [window_mass] using NorthHistory.mass_tendsto N
  apply summable_of_sum_le (fun D=>D.weight_nonneg hN)
  intro F
  apply ge_of_tendsto hlim
  filter_upwards [tendsto_atTop.mp (window_tendsto N) F] with m hm
  exact Finset.sum_le_sum_of_subset_of_nonneg hm (fun D _ _=>D.weight_nonneg hN)

 

theorem tsum_weight (N : ℕ) (hN : 1≤N) :
    (∑' D : CrossTopArch N,D.weight)=realNorthSeparator N := by
  let : Fact (1≤N) := ⟨hN⟩
  have h₁ := (summable_weight N hN).hasSum.comp (window_tendsto N)
  have h₂ : Tendsto (fun m : ℕ=>∑D∈window N m,D.weight) atTop (𝓝 (realNorthSeparator N)) := by
    simpa only [window_mass] using NorthHistory.mass_tendsto N
  exact tendsto_nhds_unique h₁ h₂

end CrossTopArch
end

 

 

noncomputable section
open scoped Classical BigOperators
open Diagram

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

lemma weight_nonneg (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a≠b) :
    0≤D.toHoneycombAssignment.weight := by
  rw [←D.weight_toArch hN,(D.toArch hN).weight_eq_path hN (by
    intro he; have hx:=BoundaryPort.bottom.inj he; omega)]
  exact (pow_pos rho_pos _).le

lemma weight_sum (N : ℕ) (hN : 1≤N) (a b : ℤ) (hab : a≠b) :
    (∑' D : TopArchConfiguration N a b,D.toHoneycombAssignment.weight)=K N (b-a) := by
  rw [HoneycombConfiguration.arch_sum N hN (b-a) (by omega)]
  rw [show (fun D : TopArchConfiguration N a b=>D.toHoneycombAssignment.weight)=
      (fun D : TopArchConfiguration N a b=>(D.toArch hN).weight) from
    funext (fun D=>(D.weight_toArch hN).symm)]
  exact (equivArch N a b hN).tsum_eq HoneycombConfiguration.weight

lemma summable_weight_iff (N : ℕ) (hN : 1≤N) (a b : ℤ) (hab : a≠b) :
    Summable (fun D : TopArchConfiguration N a b=>D.toHoneycombAssignment.weight) ↔
      Summable (archWeight N (b-a)) := by
  rw [HoneycombConfiguration.arch_summable N hN (b-a) (by omega)]
  have hh := (equivArch N a b hN).summable_iff (f:=HoneycombConfiguration.weight)
  have he : HoneycombConfiguration.weight ∘ (equivArch N a b hN)=
      fun D : TopArchConfiguration N a b=>D.toHoneycombAssignment.weight := by
    funext D
    exact D.weight_toArch hN
  rwa [he] at hh

end TopArchConfiguration

namespace CrossTopArch

def sigmaEquiv (N : ℕ) : CrossTopArch N ≃
    Sigma (fun x : ℕ×ℕ=>TopArchConfiguration N (-1-(x.1:ℤ)) (x.2:ℤ)) where
  toFun D := ⟨(D.left,D.right),D.arch⟩
  invFun D := ⟨D.1.1,D.1.2,D.2⟩
  left_inv D := by cases D; rfl
  right_inv D := by rcases D with ⟨⟨l,r⟩,D⟩; rfl

lemma summable_sigma (N : ℕ) (hN : 1≤N) :
    Summable (fun D : Sigma (fun x : ℕ×ℕ=>TopArchConfiguration N (-1-(x.1:ℤ)) (x.2:ℤ))=>
      D.2.toHoneycombAssignment.weight) :=
  (sigmaEquiv N).summable_iff.mp (summable_weight N hN)

lemma sigma_sums (N : ℕ) (hN : 1≤N) :
    (∀ x : ℕ×ℕ,Summable (fun D : TopArchConfiguration N (-1-(x.1:ℤ)) (x.2:ℤ)=>
      D.toHoneycombAssignment.weight)) ∧
    Summable (fun x : ℕ×ℕ=>K N ((x.1+x.2:ℕ)+1)) := by
  have hh := (summable_sigma_of_nonneg (fun D : Sigma (fun x : ℕ×ℕ=>TopArchConfiguration N (-1-(x.1:ℤ)) (x.2:ℤ))=>
    TopArchConfiguration.weight_nonneg D.2 hN (by omega))).mp (summable_sigma N hN)
  refine ⟨hh.1,hh.2.congr ?_⟩
  intro x
  rw [TopArchConfiguration.weight_sum N hN _ _ (by omega)]
  congr 1
  omega

end CrossTopArch

 

theorem archWeight_summable_positive {N : ℕ} (hN : 1≤N) (k : ℤ) (hk : 0<k) :
    Summable (archWeight N k) := by
  have hh := (TopArchConfiguration.summable_weight_iff N hN
    (-1-((k.toNat-1:ℕ):ℤ)) 0 (by omega)).mp ((CrossTopArch.sigma_sums N hN).1 (k.toNat-1,0))
  convert hh using 1
  congr 1
  omega

theorem archWeight_summable {N : ℕ} (hN : 1≤N) (k : ℤ) : Summable (archWeight N k) := by
  rcases lt_trichotomy k 0 with hk|rfl|hk
  · have hp := archWeight_summable_positive hN (-k) (by omega)
    let e:=mirrorTriangles_involutive.toPerm _
    have hh := (e.summable_iff).mpr hp
    apply hh.congr
    intro p
    exact archWeight_mirror N k p
  · change Summable (fun p : List Triangle=>archWeight N 0 p)
    simp only [archWeight,ne_eq,not_true_eq_false,false_and,ite_false]
    exact summable_zero
  · exact archWeight_summable_positive hN k hk

 

theorem moment_summable {N : ℕ} (hN : 1≤N) :
    Summable (fun k : ℕ=>(k+1:ℝ)*K N (k+1)) := by
  apply (summable_add_diagonal_iff (fun n=>K_nonneg N (n+1))).mp
  exact (CrossTopArch.sigma_sums N hN).2

 

theorem moment_eq_realNorthSeparator {N : ℕ} (hN : 1≤N) :
    moment N=realNorthSeparator N := by
  rw [←CrossTopArch.tsum_weight N hN]
  have hs:=CrossTopArch.summable_sigma N hN
  have he : (∑' D : CrossTopArch N,D.weight)=
      ∑' D : Sigma (fun x : ℕ×ℕ=>TopArchConfiguration N (-1-(x.1:ℤ)) (x.2:ℤ)),
        D.2.toHoneycombAssignment.weight :=
    (CrossTopArch.sigmaEquiv N).tsum_eq (fun D=>D.2.toHoneycombAssignment.weight)
  rw [he,hs.tsum_sigma' ((CrossTopArch.sigma_sums N hN).1)]
  have hi (x : ℕ×ℕ) :
      (∑' D : TopArchConfiguration N (-1-(x.1:ℤ)) (x.2:ℤ),D.toHoneycombAssignment.weight)=
        K N ((x.1+x.2:ℕ)+1) := by
    rw [TopArchConfiguration.weight_sum N hN _ _ (by omega)]
    congr 1
    omega
  simp_rw [hi]
  exact (tsum_add_diagonal (fun n=>K_nonneg N (n+1)) (moment_summable hN)).symm

 

theorem physical_arch_formula {N : ℕ} (hN : 1≤N) :
    ∃ g : Polynomial ℝ, MonicProblem N g ∧ moment N=(N:ℝ)*C-eta*g.coeff (N-1) := by
  rw [moment_eq_realNorthSeparator hN]
  exact realNorthSeparator_arch hN

 
theorem physical_moment_growth : Comparable moment (fun N=>(N:ℝ)^(3/4:ℝ)) := by
  obtain ⟨lo,hi,hl,hh,hg⟩:=homogeneous_arch_coefficient_growth
  refine ⟨lo,hi,hl,hh,?_⟩
  intro N hN
  obtain ⟨g,hgm,he⟩:=physical_arch_formula hN
  simpa only [he] using hg N hN g hgm

end
end CriticalStrip

end OAI
