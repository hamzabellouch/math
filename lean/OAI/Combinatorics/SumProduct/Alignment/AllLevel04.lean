import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators Topology
end
 
end

section
 

 

noncomputable section
open scoped Topology
open Filter
universe u
namespace AllLevelRemovals
open RationalLattice
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (L : ℕ → ℝ) (s : ℕ)

structure Removal where
  flow : Multiplicative ℝ →* G
  continuous : Continuous flow
  rational_unit : IsRational c (flow (Multiplicative.ofAdd 1))
  degree : ℕ
  degree_pos : 0<degree
  degree_le : degree ≤ s
  integer : ℕ → ℤ
  small : ℕ → ℝ
  bound : ℝ
  bound_nonneg : 0≤bound
  small_bound : ∀ N,|small N|≤bound/(L N)^degree
  limit : ℝ
  scaled_tendsto : Tendsto (fun N=>(L N)^degree*small N) atTop (𝓝 limit)

namespace Removal
variable {c L s}
def left (W : Removal c L s) (N : ℕ) (z : ℤ) : G :=
  W.flow (Multiplicative.ofAdd (W.small N)) ^ Ring.choose z W.degree

def right (W : Removal c L s) (N : ℕ) (z : ℤ) : G :=
  W.flow (Multiplicative.ofAdd 1) ^ (W.integer N * Ring.choose z W.degree)

omit [IsTopologicalGroup G] in
lemma flow_int [IsTopologicalGroup G] (W : Removal c L s) (z : ℤ) :
    W.flow (Multiplicative.ofAdd (z:ℝ))=W.flow (Multiplicative.ofAdd 1)^z := by
  have h:=W.flow.map_zpow (Multiplicative.ofAdd 1) z
  change W.flow (Multiplicative.ofAdd (z • (1:ℝ)))=_ at h
  simpa only [zsmul_eq_mul,mul_one] using h

lemma right_eq (W : Removal c L s) (N : ℕ) (z : ℤ) :
    W.right N z=W.flow (Multiplicative.ofAdd (W.integer N:ℝ))^Ring.choose z W.degree := by
  rw [flow_int,← zpow_mul]
  rfl

def reindex (W : Removal c L s) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Removal c (L∘φ) s where
  flow := W.flow
  continuous := W.continuous
  rational_unit := W.rational_unit
  degree := W.degree
  degree_pos := W.degree_pos
  degree_le := W.degree_le
  integer := W.integer∘φ
  small := W.small∘φ
  bound := W.bound
  bound_nonneg := W.bound_nonneg
  small_bound := fun N=>W.small_bound (φ N)
  limit := W.limit
  scaled_tendsto := W.scaled_tendsto.comp hφ.tendsto_atTop

omit [IsTopologicalGroup G] in
@[simp] lemma reindex_left [IsTopologicalGroup G] (W : Removal c L s) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (N : ℕ) (z : ℤ) : (W.reindex φ hφ).left N z=W.left (φ N) z := rfl
omit [IsTopologicalGroup G] in
@[simp] lemma reindex_right [IsTopologicalGroup G] (W : Removal c L s) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (N : ℕ) (z : ℤ) : (W.reindex φ hφ).right N z=W.right (φ N) z := rfl
end Removal

variable {c L s}
def leftWord (W : List (Removal c L s)) (N : ℕ) (z : ℤ) : G :=
  (W.map (fun w=>w.left N z)).prod

def rightWord (W : List (Removal c L s)) (N : ℕ) (z : ℤ) : G :=
  (W.reverse.map (fun w=>w.right N z)).prod

omit [IsTopologicalGroup G] in
@[simp] lemma leftWord_nil [IsTopologicalGroup G] (N : ℕ) (z : ℤ) : leftWord ([]:List (Removal c L s)) N z=1 := rfl
omit [IsTopologicalGroup G] in
@[simp] lemma rightWord_nil [IsTopologicalGroup G] (N : ℕ) (z : ℤ) : rightWord ([]:List (Removal c L s)) N z=1 := rfl

omit [IsTopologicalGroup G] in
lemma leftWord_append [IsTopologicalGroup G] (W : List (Removal c L s)) (w : Removal c L s) (N : ℕ) (z : ℤ) :
    leftWord (W++[w]) N z=leftWord W N z*w.left N z := by
  simp [leftWord]
omit [IsTopologicalGroup G] in
lemma rightWord_append [IsTopologicalGroup G] (W : List (Removal c L s)) (w : Removal c L s) (N : ℕ) (z : ℤ) :
    rightWord (W++[w]) N z=w.right N z*rightWord W N z := by
  simp [rightWord]

omit [IsTopologicalGroup G] in
lemma leftWord_reindex [IsTopologicalGroup G] (W : List (Removal c L s)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (N : ℕ) (z : ℤ) :
    leftWord (W.map (fun w=>w.reindex φ hφ)) N z=leftWord W (φ N) z := by
  simp only [leftWord,List.map_map]
  rfl
omit [IsTopologicalGroup G] in
lemma rightWord_reindex [IsTopologicalGroup G] (W : List (Removal c L s)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (N : ℕ) (z : ℤ) :
    rightWord (W.map (fun w=>w.reindex φ hφ)) N z=rightWord W (φ N) z := by
  simp only [rightWord,← List.map_reverse,List.map_map]
  rfl

end AllLevelRemovals
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology commutatorElement
open Filter
universe u
namespace AllLevelStates
open RationalLattice CubeFaces NilpotentTaylor AllLevelFactorization
open AllLevelDomains AllLevelRemovals CubeHorizontalIrrationality
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (Γ : Subgroup G) (s : ℕ)
variable (K : Filtration G) (P : ℕ → ℤ → G) (L : ℕ → ℝ)

structure State where
  domain : Domain c Γ s
  subseq : ℕ → ℕ
  strictmono : StrictMono subseq
  coeff : ℕ → ∀ k : ℕ,domain.filtration.level k
  zero : ∀ N,(coeff N 0).val=1
  level_image : ∀ k (x : domain.Carrier),x∈domain.filtration.level k →
    domain.embed x∈K.level k
  removals : List (Removal c (L∘subseq) s)
  realization : ∀ N z,P (subseq N) z=leftWord removals N z *
    domain.embed (word (fun k=>(coeff N k).val) (s+1) z)*rightWord removals N z

namespace State
variable {c Γ s K P L}
variable (S : State c Γ s K P L)

def Irrational : Prop := ∀ j : ℕ, 0 < j → j ≤ s →
  ∀ χ : S.domain.filtration.level j →* Multiplicative ℝ,
    χ≠1 → Continuous χ → RationalCharacter S.domain.lattice χ →
    (∀ x : S.domain.filtration.level j,x.val∈S.domain.filtration.level (j+1) → χ x=1) →
    (∀ a b : ℕ,0<a → 0<b → a+b=j →
      ∀ x∈S.domain.filtration.level a,∀ y∈S.domain.filtration.level b,
        ∀ hc : ⁅x,y⁆∈S.domain.filtration.level j,χ ⟨⁅x,y⁆,hc⟩=1) →
    Tendsto (fun N=>|L (S.subseq N)|^j*
      TriangularLatticeRecovery.circleNorm ((χ (S.coeff N j)).toAdd)) atTop atTop

lemma monoidHom_word {A B : Type*} [Group A] [Group B] (f : A →* B)
    (a : ℕ → A) (d : ℕ) (z : ℤ) : f (word a d z)=word (fun k=>f (a k)) d z := by
  induction d with
  | zero => simp [word]
  | succ d ih => simp only [word,Pi.mul_apply,map_mul,map_zpow,ih]

 

omit [IsTopologicalGroup G] in
lemma lift_coefficients [IsTopologicalGroup G] (j : ℕ) (hj : 0<j)
    (χ : S.domain.filtration.level j →* Multiplicative ℝ)
    (hnext : ∀ x : S.domain.filtration.level j,
      x.val∈S.domain.filtration.level (j+1) → χ x=1)
    (hbr : ∀ a b : ℕ,0<a → 0<b → a+b=j →
      ∀ x∈S.domain.filtration.level a,∀ y∈S.domain.filtration.level b,
        ∀ hc : ⁅x,y⁆∈S.domain.filtration.level j,χ ⟨⁅x,y⁆,hc⟩=1)
    (E : Domain c Γ s) (J : E.Carrier →* S.domain.Carrier)
    (hJ : Function.Injective J)
    (hrange : J.range=(S.domain.refinedFiltration j hj χ hnext hbr).level 1)
    (hlevels : ∀ k (x : E.Carrier),x∈E.filtration.level k ↔
      J x∈(S.domain.refinedFiltration j hj χ hnext hbr).level k)
    (b : ℕ → S.domain.Carrier)
    (hb : ∀ i<s+1,b i∈(S.domain.refinedFiltration j hj χ hnext hbr).level i)
    (hb0 : b 0=1) :
    ∃ a : ∀ k : ℕ,E.filtration.level k,
      (a 0).val=1 ∧ ∀ k<s+1,J (a k).val=b k := by
  classical
  let F:=S.domain.refinedFiltration j hj χ hnext hbr
  have he (k : ℕ) (hk : k<s+1) : ∃ x : E.Carrier,J x=b k := by
    apply (hrange ▸ (show b k∈F.level 1 from ?_))
    by_cases hk0 : k=0
    · subst k; rw [hb0]; exact (F.level 1).one_mem
    · exact F.antitone (by omega) (hb k hk)
  choose f hf using he
  let a : ∀ k : ℕ,E.filtration.level k:=fun k=>
    if hk : k<s+1 then ⟨f k hk,(hlevels k _).mpr ((hf k hk) ▸ hb k hk)⟩ else 1
  refine ⟨a,?_,?_⟩
  · apply hJ
    have hh:=hf 0 (by omega)
    simpa [a,hb0,map_one] using hh
  · intro k hk
    change J ((if h : k<s+1 then (⟨f k h,_⟩ : E.filtration.level k) else 1).val)=b k
    rw [dite_eq_left hk]
    exact hf k hk

end State
end AllLevelStates
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology commutatorElement
open Filter
universe u
namespace AllLevelStates
open RationalLattice CubeFaces NilpotentTaylor AllLevelFactorization
open AllLevelDomains AllLevelRemovals CubeHorizontalIrrationality
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G} {s : ℕ}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
namespace State

 

theorem descend_integral (S : State c Γ s K P L) (hL : ∀ N,0<L N)
    (j : ℕ) (hj : 0<j) (hjs : j ≤ s)
    (χ : S.domain.filtration.level j →* Multiplicative ℝ)
    (hne : χ≠1) (hcont : Continuous χ)
    (hz : ∀ x : S.domain.filtration.level j,x.val∈S.domain.lattice →
      ∃ z : ℤ,(χ x).toAdd=z)
    (hnext : ∀ x : S.domain.filtration.level j,
      x.val∈S.domain.filtration.level (j+1) → χ x=1)
    (hbr : ∀ a b : ℕ,0<a → 0<b → a+b=j →
      ∀ x∈S.domain.filtration.level a,∀ y∈S.domain.filtration.level b,
        ∀ hc : ⁅x,y⁆∈S.domain.filtration.level j,χ ⟨⁅x,y⁆,hc⟩=1)
    (hbad : ¬ Tendsto (fun N=>|L (S.subseq N)|^j*
      TriangularLatticeRecovery.circleNorm ((χ (S.coeff N j)).toAdd)) atTop atTop) :
    ∃ T : State c Γ s K P L,T.domain.rank<S.domain.rank := by
  classical
  let D:=S.domain
  obtain ⟨φ,hφ,m,δ,C,hC,a,hdecomp,hbound,htendsto⟩:=
    LevelCharacterSubsequence.small_remainder_subsequence (L∘S.subseq)
      (fun N=>(χ (S.coeff N j)).toAdd) j (fun N=>hL _) hbad
  obtain ⟨flow,hflow,hunit,hrational⟩:=RationalLevelFlow.exists_unit_flow
    D.chart D.secondKind D.lattice (D.filtration.level j) D.integer_lattice
    (D.cutoff j) (D.cutoff_le j) (D.adapted j) χ hcont hz hne
  obtain ⟨E,J,hJcont,hJinj,heembed,hrange,hlevels,hrank⟩:=
    D.exists_refinement j hj hjs χ hnext hbr hcont hz hne
  let F:=D.refinedFiltration j hj χ hnext hbr
  let ν:=S.subseq∘φ
  have hν : StrictMono ν:=S.strictmono.comp hφ
  let w : Removal c (L∘ν) s:=
    { flow := D.embed.comp ((D.filtration.level j).subtype.comp flow)
      continuous := D.continuous.comp (continuous_subtype_val.comp hflow)
      rational_unit := D.rational_image _ hrational
      degree := j
      degree_pos := hj
      degree_le := hjs
      integer := m
      small := δ
      bound := C
      bound_nonneg := hC
      small_bound := hbound
      limit := a
      scaled_tendsto := htendsto }
  let u (N : ℕ):=flow (Multiplicative.ofAdd (δ N))
  let v (N : ℕ):=flow (Multiplicative.ofAdd (m N:ℝ))
  have hb (N : ℕ) : ∃ b : ℕ → D.Carrier,
      (∀ i<s+1,b i∈F.level i) ∧
      (∀ i<j,b i=(S.coeff (φ N) i).val) ∧
      (∀ z : ℤ,((u N).val^Ring.choose z j)⁻¹ *
        word (fun k=>(S.coeff (φ N) k).val) (s+1) z *
          ((v N).val^Ring.choose z j)⁻¹=word b (s+1) z) := by
    apply one_level_descent D.filtration (D.zero_top.trans D.one_top.symm)
      j hj χ hnext hbr (s+1) D.terminal (by omega)
      (fun k=>(S.coeff (φ N) k).val) (fun i _=>(S.coeff (φ N) i).property)
      (S.zero (φ N)) (u N) (v N)
    change (χ (flow (Multiplicative.ofAdd (δ N)))).toAdd+
      (χ (flow (Multiplicative.ofAdd (m N:ℝ)))).toAdd=(χ (S.coeff (φ N) j)).toAdd
    rw [hunit,hunit,hdecomp N]
    ring
  choose b hbmem hblow hbword using hb
  have hbzero (N : ℕ) : b N 0=1:=(hblow N 0 hj).trans (S.zero (φ N))
  have hac (N : ℕ) : ∃ ac : ∀ k : ℕ,E.filtration.level k,
      (ac 0).val=1 ∧ ∀ k<s+1,J (ac k).val=b N k :=
    S.lift_coefficients j hj χ hnext hbr E J hJinj hrange hlevels
      (b N) (hbmem N) (hbzero N)
  choose ac hac0 hac using hac
  have hword (N : ℕ) (z : ℤ) :
      J (word (fun k=>(ac N k).val) (s+1) z)=word (b N) (s+1) z := by
    rw [monoidHom_word]
    exact congrFun (word_congr (s+1) (hac N)) z
  have hleft (N : ℕ) (z : ℤ) :
      w.left N z=D.embed ((u N).val^Ring.choose z j) := by
    simp only [Removal.left,w,u,MonoidHom.coe_comp,Function.comp_apply,
      Subgroup.coe_subtype,map_zpow]
  have hright (N : ℕ) (z : ℤ) :
      w.right N z=D.embed ((v N).val^Ring.choose z j) := by
    rw [Removal.right_eq]
    simp only [w,v,MonoidHom.coe_comp,Function.comp_apply,Subgroup.coe_subtype,map_zpow]
  let W₀ : List (Removal c (L∘ν) s):=S.removals.map (fun w=>w.reindex φ hφ)
  let W : List (Removal c (L∘ν) s):=W₀ ++ [w]
  let T : State c Γ s K P L:=
    { domain := E
      subseq := ν
      strictmono := hν
      coeff := ac
      zero := hac0
      level_image := by
        intro k x hx
        rw [heembed]
        apply S.level_image k
        have hh:=(hlevels k x).mp hx
        exact shrinkLevel_le D.filtration j (levelKernel D.filtration j χ)
          (levelKernel_le D.filtration j χ) k hh
      removals := W
      realization := by
        intro N z
        change P (S.subseq (φ N)) z=leftWord W N z*
          E.embed (word (fun k=>(ac N k).val) (s+1) z)*rightWord W N z
        rw [S.realization]
        simp only [W,W₀,leftWord_append,rightWord_append,leftWord_reindex,rightWord_reindex]
        rw [hleft,hright,heembed,hword]
        have he : word (fun k=>(S.coeff (φ N) k).val) (s+1) z=
            (u N).val^Ring.choose z j*word (b N) (s+1) z*(v N).val^Ring.choose z j := by
          rw [← hbword N z]
          group
        rw [he,map_mul,map_mul]
        dsimp only [D]
        group }
  exact ⟨T,hrank⟩

end State
end AllLevelStates

end
end
end
end

end OAI
