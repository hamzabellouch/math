import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators commutatorElement
end
 
end

section
 

 

noncomputable section
open Topology
open scoped BigOperators commutatorElement
universe u
namespace AllLevelDomains
open RationalLattice MalcevCharacters CubeFaces AllLevelFactorization AllLevelGeometry
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (Γ : Subgroup G) (s : ℕ)

structure Domain where
  Carrier : Type u
  [group : Group Carrier]
  [topology : TopologicalSpace Carrier]
  [topGroup : IsTopologicalGroup Carrier]
  embed : Carrier →* G
  injective : Function.Injective embed
  continuous : Continuous embed
  closedEmbedding : IsClosedEmbedding embed
  dim : ℕ
  chart : RealCoordinates Carrier dim
  secondKind : SecondKind chart
  lattice : Subgroup Carrier
  integer_lattice : ∀ x : Carrier,x∈lattice ↔ ∀ i,∃ z : ℤ,chart.coord x i=z
  lattice_image : ∀ x : Carrier,x∈lattice → embed x∈Γ
  rational_image : ∀ x : Carrier,IsRational chart x → IsRational c (embed x)
  filtration : Filtration Carrier
  zero_top : filtration.level 0=⊤
  one_top : filtration.level 1=⊤
  terminal : filtration.level (s+1)=⊥
  cutoff : ℕ → ℕ
  cutoff_le : ∀ k,cutoff k≤dim
  adapted : ∀ k (x : Carrier),x∈filtration.level k ↔
    ∀ i : Fin dim,i.val<cutoff k → chart.coord x i=0
attribute [instance] Domain.group Domain.topology Domain.topGroup

namespace Domain
variable {c Γ s}
def rank (D : Domain c Γ s) : ℕ := AllLevelGeometry.rank D.dim s D.cutoff

omit [IsTopologicalGroup G] in
lemma level_closed [IsTopologicalGroup G] (D : Domain c Γ s) (k : ℕ) :
    IsClosed (D.filtration.level k : Set D.Carrier) := by
  have hc : IsClosed {x : D.Carrier|∀ i : Fin D.dim,i.val<D.cutoff k → D.chart.coord x i=0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i=>isClosed_iInter fun _=>isClosed_eq
      ((continuous_apply i).comp D.chart.coord.continuous) continuous_const
  convert hc using 1
  ext x
  exact D.adapted k x

variable (D : Domain c Γ s) (j : ℕ) (hj : 0<j) (hjs : j ≤ s)
variable (χ : D.filtration.level j →* Multiplicative ℝ)
variable (hnext : ∀ x : D.filtration.level j,x.val∈D.filtration.level (j+1) → χ x=1)
variable (hbr : ∀ a b : ℕ,0<a → 0<b → a+b=j →
  ∀ x∈D.filtration.level a,∀ y∈D.filtration.level b,
    ∀ hc : ⁅x,y⁆∈D.filtration.level j,χ ⟨⁅x,y⁆,hc⟩=1)

abbrev refinedFiltration := kernelFiltration D.filtration (D.zero_top.trans D.one_top.symm)
  j hj χ hnext hbr

lemma refined_level_closed (hcont : Continuous χ) (k : ℕ) :
    IsClosed ((refinedFiltration D j hj χ hnext hbr).level k : Set D.Carrier) := by
  change IsClosed (shrinkLevel D.filtration j (levelKernel D.filtration j χ) k : Set D.Carrier)
  unfold shrinkLevel
  split_ifs
  · have hc : IsClosed (χ.ker : Set (D.filtration.level j)):=
      isClosed_eq hcont continuous_const
    exact (D.level_closed j).isClosedEmbedding_subtypeVal.isClosedMap _ hc
  · exact D.level_closed k

include hjs in
 

theorem exists_refinement (hcont : Continuous χ)
    (hz : ∀ x : D.filtration.level j,x.val∈D.lattice → ∃ z : ℤ,(χ x).toAdd=z)
    (hne : χ≠1) :
    ∃ E : Domain c Γ s,∃ J : E.Carrier →* D.Carrier,
      Continuous J ∧ Function.Injective J ∧
      (∀ x,E.embed x=D.embed (J x)) ∧
      J.range=(refinedFiltration D j hj χ hnext hbr).level 1 ∧
      (∀ k (x : E.Carrier),x∈E.filtration.level k ↔
          J x∈(refinedFiltration D j hj χ hnext hbr).level k) ∧
      E.rank<D.rank := by
  let F:=refinedFiltration D j hj χ hnext hbr
  let K:=F.level 1
  obtain ⟨q,d,Δ,t,hd,hΔ,hle,hrat,ht,hadapt,hrank⟩:=restricted_refinement
    D.chart D.filtration D.zero_top D.one_top D.cutoff D.cutoff_le D.adapted
    j hj χ hnext hbr D.secondKind D.lattice D.integer_lattice hcont hz hne s hjs
  have h01 : F.level 0=F.level 1 := shrink_zero_one D.filtration
    (D.zero_top.trans D.one_top.symm) j hj (levelKernel D.filtration j χ)
    (levelKernel_le D.filtration j χ) (next_le_levelKernel D.filtration j χ hnext)
    (brackets_le_levelKernel D.filtration j χ hbr)
  have hbottom : F.level (s+1)=⊥ := by
    apply le_antisymm _ bot_le
    have hle:=shrinkLevel_le D.filtration j (levelKernel D.filtration j χ)
      (levelKernel_le D.filtration j χ) (s+1)
    exact hle.trans (le_of_eq D.terminal)
  let E : Domain c Γ s :=
    { Carrier := K
      embed := D.embed.comp K.subtype
      injective := D.injective.comp Subtype.val_injective
      continuous := D.continuous.comp continuous_subtype_val
      closedEmbedding := D.closedEmbedding.comp
        ((D.refined_level_closed j hj χ hnext hbr hcont 1).isClosedEmbedding_subtypeVal)
      dim := q
      chart := d
      secondKind := hd
      lattice := Δ
      integer_lattice := hΔ
      lattice_image := fun x hx=>D.lattice_image x.val (hle x hx)
      rational_image := fun x hx=>D.rational_image x.val (hrat x hx)
      filtration := comapFiltration K.subtype F
      zero_top := by
        change (F.level 0).comap K.subtype=⊤
        rw [h01]
        ext x; simp [K]
      one_top := by
        change (F.level 1).comap K.subtype=⊤
        ext x; simp [K]
      terminal := by
        change (F.level (s+1)).comap K.subtype=⊥
        rw [hbottom]
        ext x
        change x.val=1 ↔ x=1
        constructor
        · exact fun h=>Subtype.ext h
        · exact fun h=>congrArg Subtype.val h
      cutoff := t
      cutoff_le := ht
      adapted := hadapt }
  refine ⟨E,K.subtype,continuous_subtype_val,Subtype.val_injective,fun _=>rfl,?_,?_,hrank⟩
  · exact Subgroup.range_subtype K
  · intro k x; rfl

end Domain
end AllLevelDomains
end
 
end

section
 

 

noncomputable section
open scoped Topology
open Filter
namespace LevelCharacterSubsequence
open TriangularLatticeRecovery

lemma bounded_subsequence_of_not_tendsto {f : ℕ → ℝ}
    (h : ¬ Tendsto f atTop atTop) :
    ∃ C : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, f (φ n) ≤ C := by
  rw [tendsto_atTop] at h
  push Not at h
  obtain ⟨C,hC⟩ := h
  have hf : ∃ᶠ n in atTop, f n < C := by
    simpa only [Filter.Frequently,not_le] using hC
  obtain ⟨φ,hφ,hfφ⟩:=extraction_of_frequently_atTop hf
  exact ⟨C,φ,hφ,fun n => (hfφ n).le⟩

 

theorem small_remainder_subsequence (L x : ℕ → ℝ) (j : ℕ)
    (hL : ∀ n,0<L n)
    (hbad : ¬ Tendsto (fun n => |L n|^j*circleNorm (x n)) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ m : ℕ → ℤ, ∃ δ : ℕ → ℝ,
      ∃ C : ℝ, 0≤C ∧ ∃ a : ℝ,
      (∀ n,x (φ n)=(m n:ℝ)+δ n) ∧
      (∀ n,|δ n| ≤ C/(L (φ n))^j) ∧
      Tendsto (fun n => (L (φ n))^j*δ n) atTop (𝓝 a) := by
  obtain ⟨C,φ,hφ,hC⟩:=bounded_subsequence_of_not_tendsto hbad
  let δ : ℕ → ℝ:=fun n=>x (φ n)-(round (x (φ n)):ℝ)
  have hnorm (n : ℕ) : |δ n|=circleNorm (x (φ n)) := UnitAddCircle.norm_eq.symm
  have hbd (n : ℕ) : |(L (φ n))^j*δ n| ≤ max C 0 := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg (hL _).le _),hnorm]
    have hh:=hC n
    rw [abs_of_pos (hL _)] at hh
    exact hh.trans (le_max_left _ _)
  have hmem (n : ℕ) : (L (φ n))^j*δ n∈Set.Icc (-max C 0) (max C 0) :=
    abs_le.mp (hbd n)
  obtain ⟨a,_,ψ,hψ,ha⟩:=(isCompact_Icc : IsCompact (Set.Icc (-max C 0) (max C 0))).isSeqCompact hmem
  refine ⟨φ∘ψ,hφ.comp hψ,fun n=>round (x (φ (ψ n))),δ∘ψ,max C 0,
    le_max_right _ _,a,?_,?_,?_⟩
  · intro n; dsimp [δ]; ring
  · intro n
    apply (le_div_iff₀ (pow_pos (hL _) _)).mpr
    simpa only [Function.comp_apply,abs_mul,abs_of_nonneg (pow_nonneg (hL _).le _),mul_comm]
      using hbd (ψ n)
  · exact ha

lemma nondivergence_integer_mul (L x : ℕ → ℝ) (j d : ℕ) (hd : 0<d)
    (hbad : ¬ Tendsto (fun n => |L n|^j*circleNorm (x n)) atTop atTop) :
    ¬ Tendsto (fun n => |L n|^j*circleNorm ((d:ℝ)*x n)) atTop atTop := by
  intro h
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hle (n : ℕ) : |L n|^j*circleNorm ((d:ℝ)*x n) ≤
      (d:ℝ)*(|L n|^j*circleNorm (x n)) := by
    calc _ ≤ |L n|^j*((d:ℝ)*circleNorm (x n)) :=
           mul_le_mul_of_nonneg_left (circleNorm_nat_mul d _) (pow_nonneg (abs_nonneg _) _)
         _ = _ := by ring
  have hg:=tendsto_atTop_mono hle h
  exact hbad ((tendsto_const_mul_atTop_of_pos hdR).mp hg)

end LevelCharacterSubsequence
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
namespace RationalLevelFlow
open RationalLattice MalcevCharacters RationalTailCoordinates MalcevTailSection
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)

 

omit [IsTopologicalGroup G] in
theorem continuous_flow_eq_realPower [IsTopologicalGroup G] (F : Multiplicative ℝ →* G) (hF : Continuous F)
    (t : ℝ) : F (Multiplicative.ofAdd t)=realPower c (F (Multiplicative.ofAdd 1)) t := by
  let f : ℝ → G := fun t => F (Multiplicative.ofAdd t)
  let g : ℝ → G := realPower c (f 1)
  have hf : Continuous f := hF.comp continuous_ofAdd
  have hg : Continuous g := realPower_continuous c _
  have hfa (s t : ℝ) : f (s+t)=f s*f t := F.map_mul _ _
  have hga (s t : ℝ) : g (s+t)=g s*g t := realPower_add c _ _ _
  have hfg1 : f 1=g 1 := by simp only [g,realPower_one]
  have hcoord : ∀ k : ℕ,∀ i : Fin n,i.val=k→∀ t : ℝ,
      c.coord (f t) i=c.coord (g t) i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      have hl (a : Fin i.val) (s : ℝ) :
          c.coord (f s) ⟨a.val,lt_trans a.isLt i.isLt⟩=
            c.coord (g s) ⟨a.val,lt_trans a.isLt i.isLt⟩ :=
        ih a.val (by omega) _ rfl s
      let d : ℝ →+ ℝ :=
        { toFun := fun t => c.coord (f t) i-c.coord (g t) i
          map_zero' := by simp [f,g,c.one_coord]
          map_add' := by
            intro s t
            rw [hfa,hga,c.mul_coord,c.mul_coord]
            simp_rw [hl]
            ring }
      have hd : Continuous d := ((continuous_apply i).comp (c.coord.continuous.comp hf)).sub
        ((continuous_apply i).comp (c.coord.continuous.comp hg))
      intro t
      have he:=map_real_smul d hd t 1
      have h1 : d 1=0 := by change c.coord (f 1) i-c.coord (g 1) i=0; rw [hfg1,sub_self]
      simp only [smul_eq_mul,mul_one,h1,mul_zero] at he
      exact sub_eq_zero.mp he
  exact c.coord.injective (funext (fun i=>hcoord i.val i rfl t))

section Tail
variable (hsk : SecondKind c) (Γ H : Subgroup G)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (r : ℕ) (hr : r≤n)
variable (hH : ∀ g : G,g∈H ↔ ∀ i : Fin n,i.val<r → c.coord g i=0)
variable (χ : H →* Multiplicative ℝ) (hcont : Continuous χ)
variable (hz : ∀ x : H,x.val∈Γ → ∃ z : ℤ,(χ x).toAdd=z) (hne : χ≠1)

include hsk hΓ hr hH hcont hz hne in
 

theorem exists_rational_unit : ∃ v : H,IsRational c v.val ∧ (χ v).toAdd=1 := by
  obtain ⟨q,hn⟩ : ∃ q,n=r+q := ⟨n-r,by omega⟩
  subst n
  let d:=tailCoordinates c H hH
  have dsk:=tail_secondKind c H hH hsk
  obtain ⟨k,hk⟩:=integer_character_coordinates d dsk χ (Γ.comap H.subtype)
    (tailCoordinates_lattice c H hH Γ hΓ) hcont hz
  have hk' : ∀ x : H,(χ x).toAdd=IntegerHyperplane.form k (d.coord x) := by
    intro x; rw [hk]; exact Finset.sum_congr rfl (fun i _=>mul_comm _ _)
  have hp : HasPivot k 0 := by
    by_contra hp
    apply hne
    ext x
    apply Multiplicative.toAdd.injective
    change (χ x).toAdd=0
    rw [hk']
    exact form_zero_of_no_pivot k 0 hp _ (by intro i hi; omega)
  let v:=tailSection d k 0 1
  have hrat : IsRational d v := by simpa only [Rat.cast_one] using section_rational d k 0 1
  refine ⟨v,?_,?_⟩
  · intro i
    by_cases hi : i.val<r
    · exact ⟨0,by simpa using ((hH _).mp v.property i hi).symm⟩
    · let a : Fin q:=⟨i.val-r,by omega⟩
      have he : i=embed r a := by apply Fin.ext; change i.val=r+(i.val-r); omega
      rw [he]
      exact hrat a
  · exact character_section d χ k hk' 0 1 (fun hn=>False.elim (hn hp))

include hsk hΓ hr hH hcont hz hne in
 

theorem exists_unit_flow : ∃ F : Multiplicative ℝ →* H,Continuous F ∧
    (∀ t : ℝ,(χ (F (Multiplicative.ofAdd t))).toAdd=t) ∧
    IsRational c ((F (Multiplicative.ofAdd 1)).val) := by
  obtain ⟨v,hv,hχv⟩:=exists_rational_unit c hsk Γ H hΓ r hr hH χ hcont hz hne
  let I : Set (Fin n):={i|i.val<r}
  have hHI : ∀ g : G,g∈H ↔ ∀ i∈I,c.coord g i=0 := hH
  let F : Multiplicative ℝ →* H :=
    { toFun := fun t=>subgroupRealPower c H I hHI v t.toAdd
      map_one' := subgroupRealPower_zero c H I hHI v
      map_mul' := fun s t=>subgroupRealPower_add c H I hHI v s.toAdd t.toAdd }
  refine ⟨F,(subgroupRealPower_continuous c H I hHI v).comp continuous_toAdd,?_,?_⟩
  · intro t
    change (χ (subgroupRealPower c H I hHI v t)).toAdd=t
    rw [character_subgroupRealPower c H I hHI χ hcont,hχv,mul_one]
  · change IsRational c ((subgroupRealPower c H I hHI v 1).val)
    rw [subgroupRealPower_one]
    exact hv

end Tail

end RationalLevelFlow

end
end
end
end

end OAI
