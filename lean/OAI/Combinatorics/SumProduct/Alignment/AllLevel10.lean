import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel06
import OAI.Combinatorics.SumProduct.Alignment.GlobalPoint01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter
namespace ComparableBoxLeibman

lemma halfOpen_bounds_scaled {v : ℕ} (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (c C : ℝ) (hc : 0 < c) (lo hi : ℕ → Fin v → ℝ)
    (hb : ∀ᶠ N : ℕ in atTop,
      (∀ i,c*L N ≤ hi N i-lo N i) ∧
      (∀ i,-C*L N ≤ lo N i ∧ hi N i ≤ C*L N)) :
    ∀ᶠ N : ℕ in atTop,
      (∀ i,(c/2)*L N ≤ ((⌈hi N i⌉:ℝ)-1)-lo N i) ∧
      (∀ i,-C*L N ≤ lo N i ∧ ((⌈hi N i⌉:ℝ)-1) ≤ C*L N) := by
  filter_upwards [hb,hL.eventually (eventually_ge_atTop (2/c))] with N hN hn
  have hn' : 2 ≤ c*L N := by
    have := (div_le_iff₀ hc).mp hn
    nlinarith
  constructor
  · intro i
    have hceil:=Int.le_ceil (hi N i)
    linarith [hN.1 i]
  · intro i
    constructor
    · exact (hN.2 i).1
    · have hceil:=Int.ceil_lt_add_one (hi N i)
      linarith [(hN.2 i).2]

lemma affine_bounds_scaled {v : ℕ} (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) (d : ℕ) (hd : 0 < d)
    (r : Fin v → ℤ) (lo hi : ℕ → Fin v → ℝ)
    (hb : ∀ᶠ N : ℕ in atTop,
      (∀ i,c*L N ≤ hi N i-lo N i) ∧
      (∀ i,-C*L N ≤ lo N i ∧ hi N i ≤ C*L N)) :
    ∃ c' C' : ℝ,0 < c' ∧ 0 < C' ∧ ∀ᶠ N : ℕ in atTop,
      (∀ i,c'*L N ≤ (hi N i-(r i:ℝ))/(d:ℝ)-(lo N i-(r i:ℝ))/(d:ℝ)) ∧
      (∀ i,-C'*L N ≤ (lo N i-(r i:ℝ))/(d:ℝ) ∧
        (hi N i-(r i:ℝ))/(d:ℝ) ≤ C'*L N) := by
  have hdR : 0 < (d:ℝ):=by exact_mod_cast hd
  let M : ℝ:=1+∑ i : Fin v,|(r i:ℝ)|
  have hM : 0 < M:=by dsimp [M]; positivity
  have hr (i : Fin v) : |(r i:ℝ)| ≤ M := by
    have hh : |(r i:ℝ)| ≤ ∑ j : Fin v,|(r j:ℝ)|:=
      Finset.single_le_sum (f:=fun j : Fin v=>|(r j:ℝ)|) (fun j _=>abs_nonneg _) (Finset.mem_univ i)
    dsimp [M]
    linarith
  refine ⟨c/d,(C+M)/d,div_pos hc hdR,div_pos (add_pos hC hM) hdR,?_⟩
  filter_upwards [hb,hL.eventually (eventually_ge_atTop 1)] with N hN hl
  constructor
  · intro i
    rw [←sub_div]
    have he : (c/(d:ℝ))*L N=(c*L N)/(d:ℝ):=by ring
    rw [he]
    apply div_le_div_of_nonneg_right _ hdR.le
    linarith [hN.1 i]
  · intro i
    have hri:=abs_le.mp (hr i)
    have hML : M ≤ M*L N:=by nlinarith
    constructor
    · apply (le_div_iff₀ hdR).mpr
      have he : (-((C+M)/(d:ℝ))*L N)*(d:ℝ)=-(C+M)*L N:=by field_simp
      rw [he]
      nlinarith [hri.2,(hN.2 i).1]
    · apply (div_le_iff₀ hdR).mpr
      have he : ((C+M)/(d:ℝ)*L N)*(d:ℝ)=(C+M)*L N:=by field_simp
      rw [he]
      nlinarith [hri.1,(hN.2 i).2]

end ComparableBoxLeibman
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter
namespace GlobalPointLaw
open CubeLocalHaar ComparableBoxLeibman

lemma cell_expect_rectangle {N d r : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (f : ℤ → ℂ) :
    (𝔼 k∈cell N d r a b,f (k.val:ℤ))=
      (𝔼 z∈physicalResidueRectangle (fun _ : Fin 1=>a*(N:ℝ))
        (fun _=>b*(N:ℝ)) (fun _=>(r:ℤ)) d,f (z 0)) := by
  have hNR : 0 < (N:ℝ):=by exact_mod_cast hN
  apply Finset.expect_bij (fun k _ _=>(k.val:ℤ))
  · intro k hk
    rw [physicalResidueRectangle_mem]
    have hh:=mem_cell.mp hk
    refine ⟨fun i=>?_,fun i=>?_⟩
    · constructor
      · exact (le_div_iff₀ hNR).mp hh.1
      · exact (div_lt_iff₀ hNR).mp hh.2.1
    · exact_mod_cast hh.2.2
  · intro k hk
    rfl
  · intro k hk l hl he
    exact Fin.ext (by exact_mod_cast congrFun he 0)
  · intro z hz
    have hz':=(physicalResidueRectangle_mem _ _ _ _ z).mp hz
    have hz0 : 0 ≤ z 0 := by
      have hh : (0:ℝ) ≤ (z 0:ℝ):=le_trans (mul_nonneg ha hNR.le) (hz'.1 0).1
      exact_mod_cast hh
    have hzN : z 0 < (N:ℤ) := by
      have hh : (z 0:ℝ) < N :=
        (hz'.1 0).2.trans_le (by nlinarith)
      exact_mod_cast hh
    let k : Fin N:=⟨(z 0).toNat,by omega⟩
    have hkz : (k.val:ℤ)=z 0:=Int.toNat_of_nonneg hz0
    have he : (fun _ : Fin 1=>(k.val:ℤ))=z := by
      funext i
      simpa only [Subsingleton.elim i 0] using hkz
    refine ⟨k,?_,he⟩
    rw [mem_cell]
    have hkR : (k.val:ℝ)=(z 0:ℝ):=by exact_mod_cast hkz
    refine ⟨(le_div_iff₀ hNR).mpr ?_,(div_lt_iff₀ hNR).mpr ?_,?_⟩
    · simpa only [hkR] using (hz'.1 0).1
    · simpa only [hkR] using (hz'.1 0).2
    · have hh:=hz'.2 0
      rw [←hkz] at hh
      exact_mod_cast hh

lemma cell_expect_progression {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (r : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (f : ℤ → ℂ) :
    (𝔼 k∈cell N d r.val a b,f (k.val:ℤ))=
      (𝔼 z∈halfOpenBox 1 (fun _ : Fin 1=>(a*(N:ℝ)-(r.val:ℝ))/(d:ℝ))
        (fun _=>(b*(N:ℝ)-(r.val:ℝ))/(d:ℝ)),f ((r.val:ℤ)+(d:ℤ)*z 0)) := by
  rw [cell_expect_rectangle hN ha hb]
  exact physicalResidueRectangle_expect _ _ _ d hd
    (fun _=>⟨by positivity,by exact_mod_cast r.isLt⟩) (fun z=>f (z 0))

lemma floor_rectangle_bounds (L : ℕ → ℝ) (ht : Tendsto L atTop atTop)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      (∀ _index : Fin 1,((b-a)/2)*L N ≤ b*(⌊L N⌋₊:ℝ)-a*(⌊L N⌋₊:ℝ)) ∧
      (∀ _index : Fin 1,-1*L N ≤ a*(⌊L N⌋₊:ℝ) ∧ b*(⌊L N⌋₊:ℝ) ≤ 1*L N) := by
  filter_upwards [ht.eventually (eventually_ge_atTop 2)] with N hN
  have hf:=Nat.floor_le (show 0 ≤ L N by linarith)
  have hf':=Nat.lt_floor_add_one (L N)
  have hf0 : 0 ≤ (⌊L N⌋₊:ℝ):=by positivity
  have hfhalf : L N/2 ≤ (⌊L N⌋₊:ℝ):=by linarith
  refine ⟨fun _=>?_,fun _=>⟨?_,?_⟩⟩
  · nlinarith
  · nlinarith
  · nlinarith

end GlobalPointLaw
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces CubeTaylorExpansion ComparableBoxLeibman CubeLocalHaar
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {F : Factorization c Γ s K P L} {r : Fin F.period} (C : F.ResidueCover r)

def pointImage : C.CubeSpace (ι:=Empty) → G⧸Γ :=
  fun x=>EmbeddedCubeHaar.coverImage F.state.domain.embed F.state.domain.filtration Γ
    (F.residue r) C.lattice C.le_induced x ∅

lemma pointImage_continuous : Continuous C.pointImage :=
  (continuous_apply ∅).comp (EmbeddedCubeHaar.coverImage_continuous F.state.domain.embed
    F.state.domain.continuous F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced)

omit [IsTopologicalGroup G] in
lemma pointImage_cubePoint (N : ℕ) (b : Option Empty → ℤ) :
    C.pointImage (C.cubePoint N b)=
      QuotientGroup.mk (F.state.domain.embed (F.structuredPart N (b none))*F.residue r) := by
  unfold pointImage cubePoint
  rw [EmbeddedCubeHaar.coverImage_mk,cubePolynomial_integer_vertex]
  simp only [Finset.sum_empty,add_zero]
  rfl

variable [MeasurableSpace (C.CubeSpace (ι:=Empty))] [BorelSpace (C.CubeSpace (ι:=Empty))]
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

def pointHaar : ProbabilityMeasure (G⧸Γ) :=
  (C.haar (ι:=Empty)).map C.pointImage

lemma pointHaar_integral (f : C(G⧸Γ,ℂ)) :
    (∫ y,f y ∂(C.pointHaar : Measure _))=
      ∫ x,f (C.pointImage x) ∂(C.haar (ι:=Empty) : Measure _) := by
  rw [pointHaar,ProbabilityMeasure.toMeasure_map]
  exact integral_map C.pointImage_continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable

 

lemma structured_local_haar (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (f : C(G⧸Γ,ℂ)) :
    Tendsto (fun N=>𝔼 k∈GlobalPointLaw.cell ⌊L (F.state.subseq N)⌋₊ F.period r.val a b,
      f (QuotientGroup.mk (F.state.domain.embed (F.structuredPart N (k.val:ℤ))*F.residue r)))
      atTop (𝓝 (∫ y,f y ∂(C.pointHaar : Measure _))) := by
  let LL : ℕ → ℝ:=L∘F.state.subseq
  have hLL : Tendsto LL atTop atTop:=ht.comp F.state.strictmono.tendsto_atTop
  let lo : ℕ → Fin 1 → ℝ:=fun N _=>(a*(⌊LL N⌋₊:ℝ)-(r.val:ℝ))/(F.period:ℝ)
  let hi : ℕ → Fin 1 → ℝ:=fun N _=>(b*(⌊LL N⌋₊:ℝ)-(r.val:ℝ))/(F.period:ℝ)
  obtain ⟨c₀,C₀,hc₀,hC₀,hbox⟩:=affine_bounds_scaled LL hLL ((b-a)/2) 1
    (by linarith) zero_lt_one F.period F.period_pos (fun _ : Fin 1=>(r.val:ℤ))
    (fun (N : ℕ) (_ : Fin 1)=>a*(⌊LL N⌋₊:ℝ)) (fun (N : ℕ) (_ : Fin 1)=>b*(⌊LL N⌋₊:ℝ))
    (GlobalPointLaw.floor_rectangle_bounds LL hLL ha hab hb)
  have hbox':=halfOpen_bounds_scaled LL hLL c₀ C₀ hc₀ lo hi hbox
  let e : Option Empty ≃ Fin 1:=Equiv.ofUnique _ _
  let ff : C(C.CubeSpace (ι:=Empty),ℂ):=f.comp ⟨C.pointImage,C.pointImage_continuous⟩
  rw [C.pointHaar_integral]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [C.haar_limit hL ht e (c₀/2) C₀ (by positivity) hC₀ F.period
    F.period_pos (fun _=>(r.val:ℤ)) {ff} isCompact_singleton ε hε,hbox',
    (tendsto_nat_floor_atTop.comp hLL).eventually (eventually_gt_atTop 0)] with N hN hh hpos
  have he:=hN (lo N) (fun i=>(⌈hi N i⌉:ℝ)-1) hh.1 hh.2 ff rfl
  have hpos' : 0 < ⌊L (F.state.subseq N)⌋₊:=hpos
  rw [GlobalPointLaw.cell_expect_progression hpos' F.period_pos r ha hb
    (fun z=>f (QuotientGroup.mk (F.state.domain.embed (F.structuredPart N z)*F.residue r)))]
  have heq (z : Fin 1 → ℤ) :
      ff (C.cubePoint N (fun i=>(r.val:ℤ)+(F.period:ℤ)*z (e i)))=
        f (QuotientGroup.mk (F.state.domain.embed
          (F.structuredPart N ((r.val:ℤ)+(F.period:ℤ)*z 0))*F.residue r)) := by
    dsimp only [ff,ContinuousMap.comp_apply,ContinuousMap.coe_mk]
    rw [C.pointImage_cubePoint]
    congr 4
  change ‖(𝔼 z∈integerBox 1 (lo N) (fun i=>(⌈hi N i⌉:ℝ)-1),
    ff (C.cubePoint N (fun i=>(r.val:ℤ)+(F.period:ℤ)*z (e i))))-
    (∫ x,f (C.pointImage x) ∂(C.haar (ι:=Empty) : Measure _))‖ < ε at he
  simpa only [dist_eq_norm,halfOpenBox,heq,lo,hi,LL,Function.comp_def] using he

end AllLevelFactorization.Factorization.ResidueCover

end
end
end

end OAI
