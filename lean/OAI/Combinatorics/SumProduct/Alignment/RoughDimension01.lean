import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughSplit01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
namespace RoughZeroDimension
open RationalLattice RoughBadBlock RoughSamplingWeights FinitePieceAverages Filter

lemma constant_mean {α : Type*} (S : Finset α) (hS : S.Nonempty) (z : ℂ) :
    mean S (fun _=>z)=z:=by
  simp only [mean,Finset.sum_const,nsmul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hS.card_pos.ne' : (S.card:ℂ)≠0),one_mul]

lemma physical_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι→ℝ) (res : ι→ℤ) (t : ℕ) (ht : 0<t)
    (hside : ∀ i,4*(t:ℝ)≤hi i-lo i) : (physicalResidueBox lo hi res t).Nonempty:=by
  rw [physical_residue_reparametrization lo hi res t ht,Finset.image_nonempty]
  apply box_nonempty _ _ _ 1 zero_lt_one
  intro i
  have htr : 0<(t:ℝ):=by exact_mod_cast ht
  dsimp [rescaledEndpoint]
  rw [←sub_div,le_div_iff₀ htr]
  simpa only [mul_one,sub_sub_sub_cancel_right] using hside i

variable {G : Type} [Group G] [TopologicalSpace G]
variable (c : RealCoordinates G 0) (Γ : Subgroup G) [MetricSpace (G⧸Γ)]

 
theorem no_block_at (v D w H : ℕ) (c₀ C₀ S Z η : ℝ) (B : NNReal)
    (hη : 0<η) (hS : 1≤S) (hZ : 8*S≤c₀*Z) :
    IsEmpty (Block c Γ v D c₀ C₀ B η w S Z H):=by
  classical
  let : Subsingleton G:=⟨fun g h=>c.coord.injective (Subsingleton.elim _ _)⟩
  let : Subsingleton (G⧸Γ):=inferInstance
  refine ⟨fun b=>?_⟩
  let j : Fin (H+1):=⟨0,by omega⟩
  have hscale:=b.scales 0 (by norm_num) (by positivity)
  simp only [mul_zero,add_zero] at hscale
  have hstart : 0<b.start:=by exact_mod_cast (show (0:ℝ)<b.start by linarith)
  have ht : 0<b.start.natAbs:=Int.natAbs_pos.mpr hstart.ne'
  have hcast : (b.start.natAbs:ℝ)=(b.start:ℝ):=by
    simp only [Nat.cast_natAbs,abs_of_nonneg (by exact_mod_cast hstart.le)]
  have hside (i) : 4*(b.start.natAbs:ℝ)≤b.hi j i-b.lo j i:=by
    rw [hcast]
    linarith [b.side j i]
  have hlarge (i) : 4*(1:ℝ)≤b.hi j i-b.lo j i:=by
    have hh : (1:ℝ)≤b.start.natAbs:=by exact_mod_cast ht
    linarith [hside i]
  have h₁:=(box_nonempty (b.lo j) (b.hi j) (fun _=>0) 1 zero_lt_one hlarge)
  have h₂:=physical_nonempty (b.lo j) (b.hi j) (b.res j) b.start.natAbs ht hside
  have hF : (fun x : Fin v→ℤ=>b.test j (QuotientGroup.mk
      (b.P (Fin.cons (j.val:ℝ) (fun i=>(x i:ℝ))))))=
      (fun _=>b.test j (QuotientGroup.mk (1:G))):=by
    funext x
    exact congrArg (b.test j) (Subsingleton.elim _ _)
  have hb:=b.bad j
  simp only [hF] at hb
  have htime : (b.start+b.step*(j.val:ℤ)).natAbs=b.start.natAbs:=by simp [j]
  rw [htime,constant_mean _ h₁,constant_mean _ h₂,sub_self,norm_zero] at hb
  exact (not_le_of_gt hη) hb

 

theorem eventually_no_zero_blocks (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hη : 0<η) {w : ℕ→ℕ} {S Z : ℕ→ℝ}
    (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop) :
    ∀ᶠ n in atTop,∀ H : ℕ,IsEmpty (Block c Γ v D c₀ C₀ B η (w n) (S n) (Z n) H):=by
  have hr : ∀ᶠ n in atTop,8/c₀≤Z n/S n:=by
    simpa only [pow_one] using (hZ 1).eventually (eventually_ge_atTop (8/c₀))
  filter_upwards [hS.eventually (eventually_ge_atTop 1),hr] with n hn hnZ
  intro H
  apply no_block_at c Γ v D (w n) H c₀ C₀ (S n) (Z n) η B hη hn
  have hh : (8/c₀)*S n≤Z n:=(le_div_iff₀ (by linarith)).mp hnZ
  have hhh:=mul_le_mul_of_nonneg_left hh hc₀.le
  field_simp at hhh
  nlinarith

end RoughZeroDimension

end
 
end

section
 

 

noncomputable section
namespace RoughDimensionInduction
open RationalLattice MalcevCharacters RoughBadBlock RoughScales Filter
open RoughBlockRationalization RoughSplitBlockReduction RoughKernelFactorization
open RoughRationalBlock PolynomialLineCoefficients CorrectedBoxLeibman

lemma divide_scale {S Z : ℕ→ℝ}
    (hZ : ∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop)
    (K : ℕ) (hK : 0<K) :
    ∀ k : ℕ,Tendsto (fun n=>(Z n/K)/S n^k) atTop atTop:=by
  intro k
  have he : (fun n=>(Z n/(K:ℝ))/S n^k)=(fun n=>(Z n/S n^k)/(K:ℝ)):=by
    funext n
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  exact Tendsto.atTop_div_const (by exact_mod_cast hK) (hZ k)

lemma eventual_reduction_scales {w : ℕ→ℕ} {S Z : ℕ→ℝ}
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop)
    (N K : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n in atTop,N≤w n ∧ K≤w n ∧ 0<S n ∧ (K:ℝ)≤Z n ∧ 1+2*S n≤δ*Z n:=by
  have hZ₀ : ∀ᶠ n in atTop,(K:ℝ)≤Z n:=by
    simpa only [pow_zero,div_one] using (hZ 0).eventually (eventually_ge_atTop (K:ℝ))
  have hZ₁ : ∀ᶠ n in atTop,3/δ≤Z n/S n:=by
    simpa only [pow_one] using (hZ 1).eventually (eventually_ge_atTop (3/δ))
  filter_upwards [hw.eventually (eventually_ge_atTop N),hw.eventually (eventually_ge_atTop K),
    hS.eventually (eventually_ge_atTop 1),hZ₀,hZ₁] with n hn hk hs hz hz'
  refine ⟨hn,hk,by linarith,hz,?_⟩
  have hh : (3/δ)*S n≤Z n:=(le_div_iff₀ (by linarith)).mp hz'
  have hlead : 3*S n≤δ*Z n:=by
    calc _=δ*((3/δ)*S n):=by field_simp
         _≤δ*Z n:=mul_le_mul_of_nonneg_left hh hδ.le
  linarith

lemma split_restrict {v s w N H : ℕ} {Z A : ℝ}
    {θ : PolynomialLineCoefficients.Grid v s→Polynomial ℝ}
    {M : PolynomialLineCoefficients.Grid v s→Polynomial ℚ}
    (hNH : N≤H) (hM : Split w H Z A θ 0 1 M) : Split w N Z A θ 0 1 M:=by
  exact ⟨hM.1,hM.2.1,fun I z hz=>hM.2.2.1 I z (hz.trans hNH),
    fun I z hz=>hM.2.2.2.1 I z (hz.trans hNH),fun z hz=>hM.2.2.2.2 z (hz.trans hNH)⟩

 

def NoLongBlocks (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : RealCoordinates G r) (_ : SecondKind c) (Γ : Subgroup G)
    (_ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (mtr : MetricSpace (G⧸Γ))
    (_ : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
    (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ),
    0<c₀ →0<C₀ →0<B →0<η →
    ∀ (w : ℕ→ℕ) (S Z : ℕ→ℝ),Tendsto w atTop atTop →Tendsto S atTop atTop →
      (∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop) →
      ∃ H : ℕ,0<H ∧ ∀ᶠ n in atTop,
        @IsEmpty (Block c Γ v D c₀ C₀ B η (w n) (S n) (Z n) H)

 

theorem no_long_blocks (r : ℕ) : NoLongBlocks r:=by
  classical
  induction r with
  | zero=>
    intro G _ _ _ c hsk Γ hΓ mtr htop v D c₀ C₀ B η hc₀ hC₀ hB hη w S Z hw hS hZ
    refine ⟨1,by omega,?_⟩
    filter_upwards [RoughZeroDimension.eventually_no_zero_blocks c Γ v D c₀ C₀ B η hc₀ hη hS hZ]
      with n hn using hn 1
  | succ r ih=>
    intro G _ _ _ c hsk Γ hΓ mtr htop v D c₀ C₀ B η hc₀ hC₀ hB hη w S Z hw hS hZ
    obtain ⟨s,U,A,hA,hrat⟩:=rationalized_block c hsk Γ hΓ htop v D c₀ C₀ B η hc₀ hC₀ hB hη hw hS hZ
    let Chars:={ξ : U // ξ.val≠1 ∧ Continuous ξ.val ∧ (∀ g∈Γ,∃ z : ℤ,(ξ.val g).toAdd=z)}
    let : Fintype Chars:=Fintype.ofFinite _
    have hred (ξ : Chars) : Nonempty (Reduction c hsk ξ.val.val Γ):=
      exists_reduction c hsk ξ.val.val Γ hΓ ξ.property.2.1 ξ.property.2.2 ξ.property.1
    let R (ξ : Chars) : Reduction c hsk ξ.val.val Γ:=Classical.choice (hred ξ)
    have hstep (ξ : Chars):=reduce_split_blocks c hsk ξ.val.val Γ (R ξ) hΓ
      ξ.property.2.1 ξ.property.2.2 htop v D s c₀ C₀ A B η hc₀ hC₀ (by linarith) hη
    choose Λ d hd hΛ D' c' hc' B' hB' δ hδ hreduce using hstep
    have hlow (ξ : Chars) : ∃ H : ℕ,0<H ∧ ∀ᶠ n in atTop,
        letI :=coordinateQuotientMetric (d ξ) (Λ ξ) (hΛ ξ)
        IsEmpty (Block (d ξ) (Λ ξ) v (D' ξ) (c' ξ) (C₀+1) (B' ξ) (η/2)
          (w n) (S n) (Z n/(R ξ).period) H):=by
      exact ih ξ.val.val.ker (d ξ) (hd ξ) (Λ ξ) (hΛ ξ)
        (coordinateQuotientMetric (d ξ) (Λ ξ) (hΛ ξ)) rfl v (D' ξ) (c' ξ) (C₀+1) (B' ξ) (η/2)
        (hc' ξ) (by linarith) (hB' ξ) (by positivity) w S (fun n=>Z n/(R ξ).period)
        hw hS (divide_scale hZ (R ξ).period (R ξ).period_pos)
    choose H hH hlow using hlow
    choose N hN using fun ξ=>hreduce ξ (H ξ) (hH ξ)
    let K:=max (2*((v+1)*s+1)) (Finset.univ.sup N)
    have hNK (ξ : Chars) : N ξ≤K:=
      (Finset.le_sup (f:=N) (Finset.mem_univ ξ)).trans (le_max_right _ _)
    obtain ⟨N₀,hN₀⟩:=hrat K (le_max_left _ _)
    have hall : ∀ᶠ n in atTop,∀ ξ : Chars,
        N ξ≤w n ∧ (R ξ).period≤w n ∧ 0<S n ∧ ((R ξ).period:ℝ)≤Z n ∧
        1+2*S n≤δ ξ*Z n ∧
        letI :=coordinateQuotientMetric (d ξ) (Λ ξ) (hΛ ξ)
        IsEmpty (Block (d ξ) (Λ ξ) v (D' ξ) (c' ξ) (C₀+1) (B' ξ) (η/2)
          (w n) (S n) (Z n/(R ξ).period) (H ξ)):=by
      apply eventually_all.mpr
      intro ξ
      filter_upwards [eventual_reduction_scales hw hS hZ (N ξ) (R ξ).period (δ ξ) (hδ ξ),
        hlow ξ] with n hn hno
      exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,hno⟩
    refine ⟨max 1 N₀,by omega,?_⟩
    filter_upwards [hN₀,hall] with n hratn hxn
    refine ⟨fun b₀=>?_⟩
    obtain ⟨b,ξ,hξ,hne,hcont,hint,θ,hθ,he,M,hM⟩:=hratn (b₀.restrict (le_max_right _ _))
    let ξ' : Chars:=⟨⟨ξ,hξ⟩,hne,hcont,hint⟩
    have hx:=hxn ξ'
    let :=coordinateQuotientMetric (d ξ') (Λ ξ') (hΛ ξ')
    let b':=b.restrict (hNK ξ')
    have he' : ∀ z : ℝ,∀ x : Fin v→ℝ,
        gridEval (fun I=>(θ I).eval z) x=(ξ'.val.val (b'.P (Fin.cons z x))).toAdd:=by
      intro z x
      simpa only [b',Block.restrict,Block.affine,Nat.cast_zero,Nat.cast_one,zero_add,one_mul,
        Fin.cons_zero,Fin.tail_cons,ξ'] using he z x
    obtain ⟨bsmall⟩:=hN ξ' (w n) (S n) (Z n) hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1
      b' θ M hθ he' (split_restrict (hNK ξ') hM)
    exact hx.2.2.2.2.2.false bsmall

end RoughDimensionInduction

end
 
end

section
 

 

noncomputable section
namespace RoughNoBadFamily
open RationalLattice MalcevCharacters RoughBadBlock Filter RoughDimensionInduction
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {r : ℕ}
variable (c : RealCoordinates G r) (hsk : SecondKind c) (Γ : Subgroup G)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

 

def BadFamily (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ) : Prop :=
  ∀ H : ℕ,∃ (w : ℕ→ℕ) (S Z : ℕ→ℝ),
    Tendsto w atTop atTop ∧ Tendsto S atTop atTop ∧
    (∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop) ∧
    ∀ᶠ n in atTop,Nonempty (Block c Γ v D c₀ C₀ B η (w n) (S n) (Z n) H)

include hsk hΓ htop in
 

theorem no_bad_family (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η) :
    ¬ BadFamily c Γ v D c₀ C₀ B η:=by
  classical
  intro hfam
  choose w S Z hw hS hZ hbad using hfam
  have hgood (H : ℕ) : ∀ᶠ n in atTop,
      H≤w H n ∧ (H:ℝ)≤S H n ∧
      (∀ k : ℕ,k≤H →(H:ℝ)≤Z H n/S H n^k) ∧
      Nonempty (Block c Γ v D c₀ C₀ B η (w H n) (S H n) (Z H n) H):=by
    have hz : ∀ᶠ n in atTop,∀ k : Fin (H+1),(H:ℝ)≤Z H n/S H n^k.val:=
      eventually_all.mpr (fun k=>(hZ H k.val).eventually (eventually_ge_atTop (H:ℝ)))
    filter_upwards [(hw H).eventually (eventually_ge_atTop H),
      (hS H).eventually (eventually_ge_atTop (H:ℝ)),hz,hbad H] with n hwn hsn hzn hbn
    exact ⟨hwn,hsn,fun k hk=>hzn ⟨k,by omega⟩,hbn⟩
  choose t ht using fun H=>(hgood H).exists
  let w' : ℕ→ℕ:=fun H=>w H (t H)
  let S' : ℕ→ℝ:=fun H=>S H (t H)
  let Z' : ℕ→ℝ:=fun H=>Z H (t H)
  have hw' : Tendsto w' atTop atTop:=by
    apply tendsto_atTop.mpr
    intro K
    filter_upwards [eventually_ge_atTop K] with n hn
    exact hn.trans (ht n).1
  have hS' : Tendsto S' atTop atTop:=by
    apply tendsto_atTop.mpr
    intro K
    obtain ⟨N,hN⟩:=exists_nat_ge K
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN.trans ((Nat.cast_le.mpr hn).trans (ht n).2.1)
  have hZ' (k : ℕ) : Tendsto (fun n=>Z' n/S' n^k) atTop atTop:=by
    apply tendsto_atTop.mpr
    intro K
    obtain ⟨N,hN⟩:=exists_nat_ge K
    filter_upwards [eventually_ge_atTop N,eventually_ge_atTop k] with n hn hk
    exact hN.trans ((Nat.cast_le.mpr hn).trans ((ht n).2.2.1 k hk))
  obtain ⟨H,hH,hno⟩:=no_long_blocks r G c hsk Γ hΓ mtr htop
    v D c₀ C₀ B η hc₀ hC₀ hB hη w' S' Z' hw' hS' hZ'
  obtain ⟨n,hn,hHn⟩:=(hno.and (eventually_ge_atTop H)).exists
  obtain ⟨b⟩:=(ht n).2.2.2
  exact hn.false (b.restrict hHn)

end RoughNoBadFamily

end
end
end

end OAI
