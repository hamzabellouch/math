import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeKernel01
import OAI.Combinatorics.SumProduct.Alignment.RoughLiteral01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end

end
 

section
 
 

noncomputable section
namespace CubeDimension
open RationalLattice MalcevCharacters RoughCubeBlock RoughScales Filter
open CubeSplitProducer CubeReduction RoughKernelFactorization CubeKernel
open RoughDimensionInduction CubeParameter

def NoLargeCubes (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : RealCoordinates G r) (_ : SecondKind c) (Γ : Subgroup G)
    (_ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
    (mtr : MetricSpace (G⧸Γ))
    (_ : mtr.toUniformSpace.toTopologicalSpace = QuotientGroup.instTopologicalSpace Γ)
    (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ),
    0 < c₀ → 0 < C₀ → 0 < B → 0 < η →
    ∀ (w : ℕ → ℕ) (S Z : ℕ → ℝ), Tendsto w atTop atTop → Tendsto S atTop atTop →
      (∀ k : ℕ, Tendsto (fun j => Z j/S j^k) atTop atTop) →
      ∃ H : ℕ, ∀ K : ℕ, ∀ᶠ j in atTop,
        @IsEmpty (Block c Γ v D c₀ C₀ B η (w j) (S j) (Z j) H K)

 

theorem no_large_cubes (r : ℕ) : NoLargeCubes r := by
  classical
  induction r with
  | zero =>
    intro G _ _ _ c hsk Γ hΓ mtr htop v D c₀ C₀ B η hc₀ hC₀ hB hη w S Z hw hS hZ
    refine ⟨0, fun K => ?_⟩
    filter_upwards [CubeZero.eventually_no_zero_cubes c Γ v D c₀ C₀ B η hc₀ hη hS hZ]
      with j hj using hj 0 K
  | succ r ih =>
    intro G _ _ _ c hsk Γ hΓ mtr htop v D c₀ C₀ B η hc₀ hC₀ hB hη w S Z hw hS hZ
    obtain ⟨q,s,U,hU,A,hA,hrat⟩ := split_producer c hsk Γ hΓ htop v D c₀ C₀ B η hc₀ hC₀ hB hη hw hS hZ
    let Chars := {ξ // ξ ∈ U}
    have hgood (ξ : Chars) : GoodCharacter Γ ξ.val := hU ξ.val ξ.property
    have hred (ξ : Chars) : Nonempty (Reduction c hsk ξ.val Γ) :=
      exists_reduction c hsk ξ.val Γ hΓ (hgood ξ).2.1 (hgood ξ).2.2 (hgood ξ).1
    let R (ξ : Chars) : Reduction c hsk ξ.val Γ := Classical.choice (hred ξ)
    have hstep (ξ : Chars) := reduce_split_cubes c hsk ξ.val Γ (R ξ) hΓ
      (hgood ξ).2.1 (hgood ξ).2.2 htop v D q s c₀ C₀ A B η hc₀ hC₀ (by linarith) hη
    choose Λ d hd hΛ D' c' hc' B' hB' δ hδ hreduce using hstep
    have hlow (ξ : Chars) : ∃ H : ℕ, ∀ K : ℕ, ∀ᶠ j in atTop,
        letI := coordinateQuotientMetric (d ξ) (Λ ξ) (hΛ ξ)
        IsEmpty (Block (d ξ) (Λ ξ) v (D' ξ) (c' ξ) (C₀+1) (B' ξ) (η/2)
          (w j) (S j) (Z j/(R ξ).period) H K) := by
      exact ih ξ.val.ker (d ξ) (hd ξ) (Λ ξ) (hΛ ξ)
        (coordinateQuotientMetric (d ξ) (Λ ξ) (hΛ ξ)) rfl v (D' ξ) (c' ξ) (C₀+1) (B' ξ) (η/2)
        (hc' ξ) (by linarith) (hB' ξ) (by positivity) w S (fun j => Z j/(R ξ).period)
        hw hS (divide_scale hZ (R ξ).period (R ξ).period_pos)
    choose H hlow using hlow
    choose N hN using fun ξ => hreduce ξ (H ξ)
    let n := max (2*(q+v*s)+1) (Finset.univ.sup N)
    have hn : 2*(q+v*s) < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    have hNn (ξ : Chars) : N ξ ≤ n :=
      (Finset.le_sup (f:=N) (Finset.mem_univ ξ)).trans (le_max_right _ _)
    obtain ⟨N₀,L₀,hN₀⟩ := hrat n hn
    refine ⟨N₀, fun K => ?_⟩
    have hall : ∀ᶠ j in atTop, ∀ ξ : Chars,
        (R ξ).period ≤ w j ∧ 0 < S j ∧ ((R ξ).period:ℝ) ≤ Z j ∧ 1+2*S j ≤ δ ξ*Z j ∧
        letI := coordinateQuotientMetric (d ξ) (Λ ξ) (hΛ ξ)
        IsEmpty (Block (d ξ) (Λ ξ) v (D' ξ) (c' ξ) (C₀+1) (B' ξ) (η/2)
          (w j) (S j) (Z j/(R ξ).period) (H ξ) ((N ξ)*(n*(L₀*(N₀*K))))) := by
      apply eventually_all.mpr
      intro ξ
      filter_upwards [eventual_reduction_scales hw hS hZ 0 (R ξ).period (δ ξ) (hδ ξ),
        hlow ξ ((N ξ)*(n*(L₀*(N₀*K))))] with j hj hno
      exact ⟨hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2,hno⟩
    filter_upwards [hN₀ K,hall] with j hj hxn
    refine ⟨fun b₀ => ?_⟩
    obtain ⟨b,χ,hχ,hsp⟩ := hj b₀
    let ξ : Chars := ⟨χ,hχ⟩
    have hx := hxn ξ
    let := coordinateQuotientMetric (d ξ) (Λ ξ) (hΛ ξ)
    let b' := b.restrict (hNn ξ)
    have hsp' : Split q s b'.P ξ.val (Z j) A :=
      split_subspace hsp (initial (N ξ) n (hNn ξ))
    obtain ⟨small⟩ := hN ξ (w j) (n*(L₀*(N₀*K))) (S j) (Z j)
      hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 b' hsp'
    exact hx.2.2.2.2.false small

end CubeDimension

end

end
 

section
 
 

noncomputable section
namespace RoughCubeDensity
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughPolynomialDegree RoughSourceExceptional RoughProgressionDensity
open CubeParameter RoughCubeBlock DenseBooleanCubes
open scoped BigOperators

def timeLift {n v : ℕ} (a m : ℤ) (h : Fin n → ℕ) (y : Fin (n+v) → ℝ) : Fin (v+1) → ℝ :=
  Fin.cons ((a:ℝ)+(m:ℝ)*∑ i, (h i:ℝ)*y (i.castAdd v)) (fun i => y (i.natAdd n))

lemma timeLift_degree {n v : ℕ} (a m : ℤ) (h : Fin n → ℕ) (i : Fin (v+1)) :
    HasDegree (fun y => timeLift a m h y i) 1 := by
  have hs : HasDegree (fun y : Fin (n+v) → ℝ => ∑ i, (h i:ℝ)*y (i.castAdd v)) 1 :=
    finite_sum Finset.univ _ _ (fun i _ => RealPolynomialDegree.scale (coordinate _) _)
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [timeLift, Fin.cons_zero, max_self] using
      RealPolynomialDegree.add (RealPolynomialDegree.const (σ:=Fin (n+v)) (a:ℝ) 1)
        (RealPolynomialDegree.scale hs (m:ℝ))
  · exact coordinate _

lemma timeLift_vertex {n v : ℕ} (a m : ℤ) (h : Fin n → ℕ) (z : Fin n → Bool) (x : Fin v → ℝ) :
    timeLift a m h (Fin.append (realVertex z) x) = Fin.cons (time a m h z:ℝ) x := by
  have he : (∑ i, (h i:ℝ)*realVertex z i) = ((∑ i, if z i then h i else 0 : ℕ):ℝ) := by
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro i _
    cases hz : z i <;> simp [realVertex, hz]
  simp only [timeLift, Fin.append_left, Fin.append_right, he, time, Int.cast_add, Int.cast_mul,
    Int.cast_natCast]

variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (c : RealCoordinates G dim) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

 

def blockOfCube {v D n K w : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η S Z : ℝ}
    (P : (Fin (v+1)→ℝ)→G) (hP : ∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D)
    (a m : ℤ) (hm : 0 < m) (hsm : Smooth w m) (h : Fin n → ℕ)
    (hh : ∀ i,0<h i ∧ h i≤K)
    (hrange : ∀ z,S≤(time a m h z:ℝ) ∧ (time a m h z:ℝ)<2*S)
    (hrough : ∀ z,Rough w (time a m h z))
    (hbad : ∀ z,BadAt Γ v c₀ C₀ B η Z P (time a m h z)) :
    RoughCubeBlock.Block c Γ v D c₀ C₀ B η w S Z n K := by
  classical
  choose lo hi res test hside hbox hlip hbound hdisc using hbad
  refine {
    start:=a, step:=m, positive:=hm, smooth:=hsm, weight:=h,
    weight_pos:=fun i=>(hh i).1, weight_bound:=fun i=>(hh i).2,
    scales:=hrange, rough:=hrough,
    P:=fun y=>P (timeLift a m h y),
    degree:=?_, lo:=lo, hi:=hi, res:=res, test:=test,
    side:=hside, box:=hbox, lip:=hlip, bound:=hbound, bad:=?_ }
  · intro i
    simpa only [one_mul] using compose (hP i) (fun j y=>timeLift a m h y j) (timeLift_degree a m h)
  · intro z
    simpa only [timeLift_vertex] using hdisc z

lemma no_dense_indices {v D H K w N : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η S Z ε : ℝ}
    (hno : IsEmpty (RoughCubeBlock.Block c Γ v D c₀ C₀ B η w S Z H K))
    (hKN : K≤N)
    (hcube : ∀ M : ℕ,K≤M → ∀ A : Finset ℕ,A⊆Finset.range M → ε*M≤(A.card:ℝ) →
      ∃ a : ℕ,∃ h : Fin H → ℕ,(∀ i,0<h i ∧ h i≤K) ∧
        ∀ z : Fin H → Bool,a+∑ i,(if z i then h i else 0)∈A)
    (P : (Fin (v+1)→ℝ)→G) (hP : ∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D)
    (a L : ℤ) (hL : 0<L) (hsm : Smooth w L) (hWL : (primorial w:ℤ)∣L)
    (ha : Rough w a)
    (hscale : ∀ i : ℕ,i<N →S≤((a+L*(i:ℤ):ℤ):ℝ) ∧ ((a+L*(i:ℤ):ℤ):ℝ)<2*S) :
    ((badIndices Γ v N c₀ C₀ B η Z P a L).card:ℝ)<ε*N := by
  classical
  by_contra! hd
  obtain ⟨u,h,hh,hverts⟩ := hcube N hKN (badIndices Γ v N c₀ C₀ B η Z P a L)
    (Finset.filter_subset _ _) hd
  have he (z : Fin H → Bool) : time (a+L*(u:ℤ)) L h z =
      a+L*((u+∑ i,if z i then h i else 0:ℕ):ℤ) := by
    simp only [time, Nat.cast_add]
    ring
  have hbad : ∀ z,BadAt Γ v c₀ C₀ B η Z P (time (a+L*(u:ℤ)) L h z) := by
    intro z
    rw [he]
    exact ((mem_badIndices Γ).mp (hverts z)).2
  have hsc : ∀ z,S≤(time (a+L*(u:ℤ)) L h z:ℝ) ∧
      (time (a+L*(u:ℤ)) L h z:ℝ)<2*S := by
    intro z
    rw [he]
    exact hscale _ ((mem_badIndices Γ).mp (hverts z)).1
  have hr : ∀ z,Rough w (time (a+L*(u:ℤ)) L h z) := by
    intro z
    rw [he]
    exact rough_add_multiple ha hWL _
  exact hno.false (blockOfCube c Γ P hP _ _ hL hsm h hh hsc hr hbad)

variable [IsTopologicalGroup G]

 

theorem source_exceptional_decay (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
    (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w : ℕ→ℕ) (S Z : ℕ→ℝ) (r L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/S n^a) atTop atTop)
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n) (hr : ∀ n,(r n).natAbs.Coprime (primorial (w n)))
    (hSL : Tendsto (fun n=>S n/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ P : (Fin (v+1)→ℝ)→G,(∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ((exceptional Γ v c₀ C₀ B η (Z n) (S n) P (r n) (L n)).card:ℝ)/
          ((times (S n) (r n) (L n)).card:ℝ)<ε := by
  classical
  obtain ⟨H,hno⟩ := CubeDimension.no_large_cubes dim G c hsk Γ hΓ mtr htop
    v D c₀ C₀ B η hc₀ hC₀ hB hη w S Z hw hS (integer_scales_of_real hS hZ)
  have ht := timeLength_tendsto (r:=r) hL hS hSL
  intro ε hε
  obtain ⟨K,hK,hcube⟩ := dense_bounded_positive_cube H ε hε
  filter_upwards [hno K,ht.eventually (eventually_ge_atTop (K:ℝ))] with j hj hNj
  intro P hP
  have hKN : K≤timeLength (S j) (r j) (L j) := by exact_mod_cast hNj
  have hN : 0<(timeLength (S j) (r j) (L j):ℝ) := by exact_mod_cast hK.trans_le hKN
  rw [exceptional_card Γ v c₀ C₀ B η (Z j) (S j) P (r j) (L j) (hL j),
    times_card _ _ _ (hL j)]
  apply (div_lt_iff₀ hN).mpr
  exact no_dense_indices c Γ hj hKN hcube P hP _ _ (hL j) (hsm j) (hWL j)
    (firstTime_rough ((rough_iff_coprime _ _).mpr (hr j)) (hWL j))
    (scale_at_index _ _ _ (hL j))

 

theorem source_literal_decay (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
    (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w : ℕ→ℕ) (S Z : ℕ→ℝ) (r L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/S n^a) atTop atTop)
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n) (hr : ∀ n,(r n).natAbs.Coprime (primorial (w n)))
    (hSL : Tendsto (fun n=>S n/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ P : (Fin (v+1)→ℝ)→G,(∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ((RoughLiteralBoxes.exceptional Γ v c₀ C₀ B η (Z n) (S n) P (r n) (L n)).card:ℝ)/
          ((times (S n) (r n) (L n)).card:ℝ)<ε := by
  classical
  have hbound := source_exceptional_decay c Γ hsk hΓ htop v D (c₀/2) (C₀+1) B η
    (by positivity) (by positivity) hB hη w S Z r L hw hS hZ hL hsm hWL hr hSL
  have hZ' : Tendsto Z atTop atTop := by
    simpa only [pow_zero, div_one] using integer_scales_of_real hS hZ 0
  intro ε hε
  filter_upwards [hbound ε hε, hZ'.eventually (eventually_ge_atTop 1),
    hZ'.eventually (eventually_ge_atTop (2/c₀))] with j hj hz hcz
  intro P hP
  have hcZ : 2≤c₀*Z j := by nlinarith [(div_le_iff₀ hc₀).mp hcz]
  have hc := Finset.card_le_card (RoughLiteralBoxes.exceptional_subset Γ v c₀ C₀ B η
    (Z j) (S j) P (r j) (L j) hz hcZ)
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)).trans_lt (hj P hP)

 

theorem rough_step (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
    (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w : ℕ→ℕ) (S Z : ℕ→ℝ) (r L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/S n^a) atTop atTop)
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n) (hr : ∀ n,(r n).natAbs.Coprime (primorial (w n)))
    (hSL : Tendsto (fun n=>S n/(L n:ℝ)) atTop atTop)
    (P : ℕ → (Fin (v+1)→ℝ)→G)
    (hP : ∀ n i,HasDegree (fun y=>canonicalLog c (P n y) i) D) :
    Tendsto (fun n =>
      ((RoughLiteralBoxes.exceptional Γ v c₀ C₀ B η (Z n) (S n) (P n) (r n) (L n)).card:ℝ)/
          ((times (S n) (r n) (L n)).card:ℝ)) atTop (nhds 0) := by
  have hh := source_literal_decay c Γ hsk hΓ htop v D c₀ C₀ B η hc₀ hC₀ hB hη
    w S Z r L hw hS hZ hL hsm hWL hr hSL
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hh ε hε] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact hn (P n) (hP n)

 

theorem finite_list_uniform {ι : Type} [Fintype ι]
    (G : ι → Type) [∀ a, Group (G a)] [∀ a, TopologicalSpace (G a)]
    [∀ a, IsTopologicalGroup (G a)] (dim : ι → ℕ)
    (c : ∀ a, RealCoordinates (G a) (dim a)) (Γ : ∀ a, Subgroup (G a))
    [mtr : ∀ a, MetricSpace ((G a)⧸(Γ a))]
    (hsk : ∀ a, SecondKind (c a))
    (hΓ : ∀ a (g : G a),g∈Γ a ↔ ∀ i,∃ z : ℤ,(c a).coord g i=z)
    (htop : ∀ a,(mtr a).toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace (Γ a))
    (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w : ℕ→ℕ) (S Z : ℕ→ℝ) (r L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/S n^a) atTop atTop)
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n) (hr : ∀ n,(r n).natAbs.Coprime (primorial (w n)))
    (hSL : Tendsto (fun n=>S n/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop, ∀ a,
      ∀ P : (Fin (v+1)→ℝ)→G a,(∀ i,HasDegree (fun y=>canonicalLog (c a) (P y) i) D) →
      ((RoughLiteralBoxes.exceptional (Γ a) v c₀ C₀ B η (Z n) (S n) P (r n) (L n)).card:ℝ)/
          ((times (S n) (r n) (L n)).card:ℝ)<ε := by
  intro ε hε
  exact eventually_all.mpr (fun a => source_literal_decay (c a) (Γ a) (hsk a) (hΓ a) (htop a)
    v D c₀ C₀ B η hc₀ hC₀ hB hη w S Z r L hw hS hZ hL hsm hWL hr hSL ε hε)

end RoughCubeDensity

end
end

end OAI
