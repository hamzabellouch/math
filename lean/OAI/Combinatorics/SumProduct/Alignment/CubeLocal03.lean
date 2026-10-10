import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeLocal02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators Topology commutatorElement
end
end
 

 
section

noncomputable section
open scoped Topology
open Filter
namespace ComparableBoxLeibman

 

def halfOpenBox (v : ℕ) (lo hi : Fin v→ℝ) : Finset (Fin v→ℤ) :=
  integerBox v lo (fun i => (⌈hi i⌉:ℝ)-1)

lemma mem_halfOpenBox {v : ℕ} (lo hi : Fin v→ℝ) (z : Fin v→ℤ) :
    z∈halfOpenBox v lo hi ↔ ∀ i,lo i≤(z i:ℝ) ∧ (z i:ℝ)<hi i := by
  rw [halfOpenBox,mem_integerBox]
  apply forall_congr'
  intro i
  apply and_congr_right
  intro _
  have hh : (z i:ℝ)≤(⌈hi i⌉:ℝ)-1 ↔ z i<⌈hi i⌉ := by
    constructor
    · intro he
      have he' : z i≤⌈hi i⌉-1 := by exact_mod_cast he
      omega
    · intro he
      have he' : z i≤⌈hi i⌉-1 := by omega
      exact_mod_cast he'
  exact hh.trans Int.lt_ceil

 

lemma halfOpen_bounds {v : ℕ} (c C : ℝ) (hc : 0<c)
    (lo hi : ℕ→Fin v→ℝ)
    (hb : ∀ᶠ N : ℕ in atTop,
      (∀ i,c*(N:ℝ)≤hi N i-lo N i) ∧
      (∀ i,-C*(N:ℝ)≤lo N i ∧ hi N i≤C*(N:ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      (∀ i,(c/2)*(N:ℝ)≤((⌈hi N i⌉:ℝ)-1)-lo N i) ∧
      (∀ i,-C*(N:ℝ)≤lo N i ∧ ((⌈hi N i⌉:ℝ)-1)≤C*(N:ℝ)) := by
  have hn : ∀ᶠ N : ℕ in atTop,2/c≤(N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2/c))
  filter_upwards [hb,hn] with N hN hn
  have hn' : 2≤c*(N:ℝ) := by
    have := (div_le_iff₀ hc).mp hn
    nlinarith
  constructor
  · intro i
    have hh := Int.le_ceil (hi N i)
    have hh' := hN.1 i
    nlinarith
  · intro i
    refine ⟨(hN.2 i).1,?_⟩
    have hh := Int.ceil_lt_add_one (hi N i)
    have hh' := (hN.2 i).2
    linarith

end ComparableBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators Topology commutatorElement
namespace CubeLocalHaar
open CubeFaces LeibmanSquare CubeTaylorExpansion CubeHorizontalIrrationality
open RationalLattice MeasureTheory Filter ComparableBoxLeibman MalcevCharacters AbelianMalcevTorus
variable {G ι : Type} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n t d v : ℕ} (c : RealCoordinates G n) (H : Filtration G)
variable (S : ℕ→Set (Fin n))
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)
variable (Λ : Subgroup G) (σ : G) (h01 : H.level 0=H.level 1)
variable (s : ℕ) (hs : H.level (s+1)=⊥) (e : Option ι≃Fin v)
variable (cc : RealCoordinates (cube H (Finset.univ : Finset ι) 0) (t+d))
variable (hsk : SecondKind cc)
variable (q : ℕ→ℕ) (hqbound : ∀ k,q k ≤ t+d)
variable (hq : ∀ k (g : cube H (Finset.univ : Finset ι) 0),
  g∈(CubeMaxFiltration.filtration H Finset.univ).level k ↔
    ∀ i : Fin (t+d),i.val < q k → cc.coord g i=0)
variable (hΓ : ∀ g : cube H (Finset.univ : Finset ι) 0,
  g∈cubeLattice H (conjugateLattice Λ σ) ↔ ∀ i,∃ z : ℤ,cc.coord g i=z)
variable [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]
variable [hBorel : @BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)) (QuotientGroup.instTopologicalSpace (cubeLattice H (conjugateLattice Λ σ))) inferInstance]
variable (mtr : MetricSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)))
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace (cubeLattice H (conjugateLattice Λ σ)))

include S hH h01 hs hsk hqbound hq hΓ htop in
 

theorem smooth_halfOpen_cube_haar
    (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)))
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure (cube H (Finset.univ : Finset ι) 0) _ μ]
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter (conjugateLattice Λ σ) ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(N:ℝ)^j)
        atTop atTop)

    (d₀ : ℕ) (hd₀ : 0<d₀) (r : Fin v→ℤ)
    (lo hi : ℝ→ℕ→Fin v→ℝ)
    (hb : ∀ α : ℝ,0<α → ∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧
      ∀ᶠ N : ℕ in atTop,
        (∀ i,c₀*(N:ℝ)≤hi α N i-lo α N i) ∧
        (∀ i,-C₀*(N:ℝ)≤lo α N i ∧ hi α N i≤C₀*(N:ℝ)))

    (g : ℕ→ℝ→G) (h : ℝ→G) (β : ℝ) (hh : ContinuousAt h β)
    (ρ : ℝ) (hρ : 0<ρ)
    (hg : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,
      ∀ t : ℝ,dist t β<ρ → dist (g N t) (h t)<ε)
    (hgeo : ∀ α : ℝ,0<α → ∀ᶠ N : ℕ in atTop,
      ∀ z∈halfOpenBox v (lo α N) (hi α N),
        |(((r (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))-β|≤α ∧
        ∀ i : ι,|(((r (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))|≤α)
    (F : C((Finset ι→G⧸Λ),ℂ)) :
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ‖(𝔼 z∈halfOpenBox v (lo α N) (hi α N),
          F (fun w : Finset ι => QuotientGroup.mk
            (g N (((r (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ)+
                ∑ i∈w,(((r (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))) *
              taylorPolynomial c H (a N) s
                (((r (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)+
                  ∑ i∈w,((r (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)) * σ)))-
        (∫ x,frozenTest H Λ σ F (fun _ => h β) x ∂μ)‖<ε := by
  have hb' : ∀ α : ℝ,0<α → ∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧
      ∀ᶠ N : ℕ in atTop,
        (∀ i,c₀*(N:ℝ)≤((⌈hi α N i⌉:ℝ)-1)-lo α N i) ∧
        (∀ i,-C₀*(N:ℝ)≤lo α N i ∧ ((⌈hi α N i⌉:ℝ)-1)≤C₀*(N:ℝ)) := by
    intro α hα
    obtain ⟨c₀,C₀,hc₀,hC₀,hbα⟩ := hb α hα
    exact ⟨c₀/2,C₀,by positivity,hC₀,halfOpen_bounds c₀ C₀ hc₀ (lo α) (hi α) hbα⟩
  exact smooth_two_scale_cube_haar c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ mtr htop
    μ a hirr d₀ hd₀ r lo (fun α N i => (⌈hi α N i⌉:ℝ)-1) hb'
    g h β hh ρ hρ hg hgeo F

end CubeLocalHaar
end
end
 

 
section

noncomputable section
open scoped Topology
open Filter
namespace CubeLocalHaar
open ComparableBoxLeibman

 

def progressionLo {v : ℕ} (a : Fin v→ℝ) (r : Fin v→ℤ) (d : ℕ)
    (N : ℕ) (i : Fin v) : ℝ := (a i*(N:ℝ)-(r i:ℝ))/(d:ℝ)
def progressionHi {v : ℕ} (a : Fin v→ℝ) (r : Fin v→ℤ) (d : ℕ)
    (α : ℝ) (N : ℕ) (i : Fin v) : ℝ := ((a i+α)*(N:ℝ)-(r i:ℝ))/(d:ℝ)

lemma progression_box_bounds {v : ℕ} (a : Fin v→ℝ) (r : Fin v→ℤ)
    (d : ℕ) (hd : 0<d) (ha : ∀ i,0≤a i ∧ a i≤1)
    (hr : ∀ i,0≤r i ∧ r i<(d:ℤ)) (α : ℝ) (hα : 0<α) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ N : ℕ in atTop,
      (∀ i,c*(N:ℝ)≤progressionHi a r d α N i-progressionLo a r d N i) ∧
      (∀ i,-C*(N:ℝ)≤progressionLo a r d N i ∧ progressionHi a r d α N i≤C*(N:ℝ)) := by
  have hd' : 0<(d:ℝ) := by exact_mod_cast hd
  have hd1 : 1≤(d:ℝ) := by exact_mod_cast hd
  refine ⟨α/(d:ℝ),α+2,div_pos hα hd',by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hN' : 1≤(N:ℝ) := by exact_mod_cast hN
  have hN0 : 0≤(N:ℝ) := by positivity
  constructor
  · intro i
    unfold progressionLo progressionHi
    have he : ((a i+α)*(N:ℝ)-(r i:ℝ))/(d:ℝ)-
        (a i*(N:ℝ)-(r i:ℝ))/(d:ℝ)=α/(d:ℝ)*(N:ℝ) := by ring
    rw [he]
  · intro i
    have ha0 := (ha i).1
    have ha1 := (ha i).2
    have hr0 : 0≤(r i:ℝ) := by exact_mod_cast (hr i).1
    have hr1 : (r i:ℝ)<(d:ℝ) := by exact_mod_cast (hr i).2
    constructor
    · unfold progressionLo
      apply (le_div_iff₀ hd').mpr
      have hpa : 0≤a i*(N:ℝ) := mul_nonneg ha0 hN0
      have hn : 1≤(α+2)*(N:ℝ) := by nlinarith
      have hdn : (d:ℝ)≤((α+2)*(N:ℝ))*(d:ℝ) := by nlinarith
      nlinarith
    · unfold progressionHi
      apply (div_le_iff₀ hd').mpr
      have hb : a i*(N:ℝ)≤(N:ℝ) := by nlinarith
      have hn : 0≤(α+2)*(N:ℝ) := mul_nonneg (by positivity) hN0
      have hdn : (α+2)*(N:ℝ)≤((α+2)*(N:ℝ))*(d:ℝ) := by nlinarith
      nlinarith

lemma progression_normalized_mem {v : ℕ} (a : Fin v→ℝ) (r : Fin v→ℤ)
    (d N : ℕ) (hd : 0<d) (hN : 0<N) (α : ℝ) (z : Fin v→ℤ)
    (hz : z∈halfOpenBox v (progressionLo a r d N) (progressionHi a r d α N))
    (i : Fin v) :
    a i≤((r i:ℝ)+(d:ℝ)*(z i:ℝ))/(N:ℝ) ∧
      ((r i:ℝ)+(d:ℝ)*(z i:ℝ))/(N:ℝ)<a i+α := by
  have hd' : 0<(d:ℝ) := by exact_mod_cast hd
  have hN' : 0<(N:ℝ) := by exact_mod_cast hN
  have hh := (mem_halfOpenBox _ _ _).mp hz i
  change (a i*(N:ℝ)-(r i:ℝ))/(d:ℝ)≤(z i:ℝ) ∧
    (z i:ℝ)<((a i+α)*(N:ℝ)-(r i:ℝ))/(d:ℝ) at hh
  have hlo := (div_le_iff₀ hd').mp hh.1
  have hhi := (lt_div_iff₀ hd').mp hh.2
  constructor
  · apply (le_div_iff₀ hN').mpr
    linarith
  · apply (div_lt_iff₀ hN').mpr
    linarith

variable {ι : Type} [Fintype ι] [DecidableEq ι] {v : ℕ}

def sourceCenter (e : Option ι≃Fin v) (β : ℝ) (i : Fin v) : ℝ :=
  if e.symm i=none then β else 0
def sourceResidue (e : Option ι≃Fin v) (r : ℕ) (i : Fin v) : ℤ :=
  if e.symm i=none then (r:ℤ) else 0

omit [Fintype ι] [DecidableEq ι] in
lemma source_box_bounds (e : Option ι≃Fin v) (β : ℝ) (hβ : β∈Set.Icc (0:ℝ) 1)
    (d r : ℕ) (hd : 0<d) (hr : r<d) (α : ℝ) (hα : 0<α) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ N : ℕ in atTop,
      (∀ i,c*(N:ℝ)≤progressionHi (sourceCenter e β) (sourceResidue e r) d α N i-
        progressionLo (sourceCenter e β) (sourceResidue e r) d N i) ∧
      (∀ i,-C*(N:ℝ)≤progressionLo (sourceCenter e β) (sourceResidue e r) d N i ∧
        progressionHi (sourceCenter e β) (sourceResidue e r) d α N i≤C*(N:ℝ)) := by
  apply progression_box_bounds _ _ d hd _ _ α hα
  · intro i
    unfold sourceCenter
    split_ifs <;> simp_all
  · intro i
    have hd' : (0:ℤ)<d := by exact_mod_cast hd
    have hr' : (r:ℤ)<d := by exact_mod_cast hr
    unfold sourceResidue
    split_ifs <;> simp_all

omit [Fintype ι] [DecidableEq ι] in
lemma source_box_geometry (e : Option ι≃Fin v) (β : ℝ)
    (d r : ℕ) (hd : 0<d) (α : ℝ) :
    ∀ᶠ N : ℕ in atTop,∀ z∈halfOpenBox v
      (progressionLo (sourceCenter e β) (sourceResidue e r) d N)
      (progressionHi (sourceCenter e β) (sourceResidue e r) d α N),
      |(((sourceResidue e r (e none)+(d:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))-β|≤α ∧
      ∀ i : ι,|(((sourceResidue e r (e (some i))+(d:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))|≤α := by
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  intro z hz
  have hh := progression_normalized_mem (sourceCenter e β) (sourceResidue e r) d N
    hd (by omega) α z hz
  constructor
  · have h := hh (e none)
    simp only [sourceCenter,Equiv.symm_apply_apply,ite_true,Int.cast_add,Int.cast_mul,
      Int.cast_natCast] at *
    rw [abs_of_nonneg (by linarith [h.1])]
    linarith [h.2]
  · intro i
    have h := hh (e (some i))
    simp only [sourceCenter,Equiv.symm_apply_apply,Option.some_ne_none,ite_false,zero_add] at h
    simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast]
    rw [abs_of_nonneg h.1]
    exact h.2.le

 

def sourceVertex (e : Option ι≃Fin v) (d r : ℕ) (z : Fin v→ℤ) (w : Finset ι) : ℤ :=
  (r:ℤ)+(d:ℤ)*(z (e none)+∑ i∈w,z (e (some i)))

omit [Fintype ι] [DecidableEq ι] in
lemma sourceVertex_emod (e : Option ι≃Fin v) (d r : ℕ) (hr : r<d)
    (z : Fin v→ℤ) (w : Finset ι) : sourceVertex e d r z w%(d:ℤ)=(r:ℤ) := by
  have hr0 : (0:ℤ)≤r := by positivity
  have hr' : (r:ℤ)<d := by exact_mod_cast hr
  simp [sourceVertex,Int.add_emod,Int.emod_eq_of_lt hr0 hr']

omit [Fintype ι] [DecidableEq ι] in
lemma sourceVertex_real (e : Option ι≃Fin v) (d r : ℕ) (z : Fin v→ℤ) (w : Finset ι) :
    (((sourceResidue e r (e none)+(d:ℤ)*z (e none):ℤ):ℝ))+
       ∑ i∈w,((sourceResidue e r (e (some i))+(d:ℤ)*z (e (some i)):ℤ):ℝ) =
      (sourceVertex e d r z w:ℝ) := by
  simp [sourceResidue,sourceVertex,mul_add,Finset.mul_sum,add_assoc]

omit [Fintype ι] [DecidableEq ι] in
lemma sourceVertex_normalized (e : Option ι≃Fin v) (d r N : ℕ)
    (z : Fin v→ℤ) (w : Finset ι) :
    (((sourceResidue e r (e none)+(d:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))+
       ∑ i∈w,((sourceResidue e r (e (some i))+(d:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ) =
      (sourceVertex e d r z w:ℝ)/(N:ℝ) := by
  rw [←Finset.sum_div,←add_div,sourceVertex_real]

end CubeLocalHaar

end
end
end
end
end

end OAI
