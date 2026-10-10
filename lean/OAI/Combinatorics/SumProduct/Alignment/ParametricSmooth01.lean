import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel04
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators Topology commutatorElement
open Filter
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology commutatorElement
open Filter
open Topology
universe u
namespace AllLevelStates
open RationalLattice CubeFaces CubePolynomials NilpotentTaylor AllLevelFactorization
open AllLevelDomains AllLevelRemovals CubeHorizontalIrrationality
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G} {s : ℕ}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
namespace State

 

theorem descend_of_not_irrational (S : State c Γ s K P L)
    (hL : ∀ N,0<L N) (hbad : ¬ S.Irrational) :
    ∃ T : State c Γ s K P L,T.domain.rank<S.domain.rank := by
  classical
  unfold Irrational at hbad
  push Not at hbad
  obtain ⟨j,hj,hjs,χ,hne,hcont,hrat,hnext,hbr,hbad⟩:=hbad
  obtain ⟨d,hd,hz⟩:=hrat
  let χ':=scaleCharacter (d:ℝ) χ
  have hne' : χ'≠1:=scaleCharacter_ne (by exact_mod_cast (Nat.ne_of_gt hd)) hne
  have hcont' : Continuous χ':=
    continuous_ofAdd.comp (continuous_const.mul (continuous_toAdd.comp hcont))
  have hnext' (x : S.domain.filtration.level j)
      (hx : x.val∈S.domain.filtration.level (j+1)) : χ' x=1 := by
    change Multiplicative.ofAdd ((d:ℝ)*(χ x).toAdd)=1
    rw [hnext x hx]
    simp
  have hbr' (a b : ℕ) (ha : 0<a) (hb : 0<b) (hab : a+b=j)
      (x : S.domain.Carrier) (hx : x∈S.domain.filtration.level a)
      (y : S.domain.Carrier) (hy : y∈S.domain.filtration.level b)
      (hc : ⁅x,y⁆∈S.domain.filtration.level j) : χ' ⟨⁅x,y⁆,hc⟩=1 := by
    change Multiplicative.ofAdd ((d:ℝ)*(χ ⟨⁅x,y⁆,hc⟩).toAdd)=1
    rw [hbr a b ha hb hab x hx y hy hc]
    simp
  exact S.descend_integral hL j hj hjs χ' hne' hcont' hz hnext' hbr'
    (LevelCharacterSubsequence.nondivergence_integer_mul (L∘S.subseq)
      (fun N=>(χ (S.coeff N j)).toAdd) j d hd hbad)

 

theorem exists_irrational_state (S₀ : State c Γ s K P L) (hL : ∀ N,0<L N) :
    ∃ S : State c Γ s K P L,S.Irrational := by
  classical
  have hex : ∃ r : ℕ,∃ S : State c Γ s K P L,S.domain.rank=r:=
    ⟨S₀.domain.rank,S₀,rfl⟩
  obtain ⟨S,hS⟩:=Nat.find_spec hex
  refine ⟨S,?_⟩
  by_contra hn
  obtain ⟨T,hT⟩:=S.descend_of_not_irrational hL hn
  have hmin:=Nat.find_min' hex (show ∃ U : State c Γ s K P L,
    U.domain.rank=T.domain.rank from ⟨T,rfl⟩)
  rw [← hS] at hmin
  exact (not_lt_of_ge hmin) hT

end State

 

def initialState (hsk : MalcevCharacters.SecondKind c)
    (hΓ : ∀ x : G,x∈Γ ↔ ∀ i,∃ z : ℤ,c.coord x i=z)
    (hK0 : K.level 0=⊤) (hK1 : K.level 1=⊤) (hKs : K.level (s+1)=⊥)
    (r : ℕ → ℕ) (hr : ∀ k,r k≤n)
    (hadapt : ∀ k (x : G),x∈K.level k ↔ ∀ i : Fin n,i.val<r k → c.coord x i=0)
    (a : ℕ → ∀ k : ℕ,K.level k) (ha0 : ∀ N,(a N 0).val=1) :
    State c Γ s K (fun N=>word (fun k=>(a N k).val) (s+1)) L where
  domain :=
    { Carrier := G
      embed := MonoidHom.id G
      injective := Function.injective_id
      continuous := continuous_id
      closedEmbedding := IsClosedEmbedding.id
      dim := n
      chart := c
      secondKind := hsk
      lattice := Γ
      integer_lattice := hΓ
      lattice_image := fun _ h=>h
      rational_image := fun _ h=>h
      filtration := K
      zero_top := hK0
      one_top := hK1
      terminal := hKs
      cutoff := r
      cutoff_le := hr
      adapted := hadapt }
  subseq := id
  strictmono := strictMono_id
  coeff := a
  zero := ha0
  level_image := fun _ _ h=>h
  removals := []
  realization := by intro N z; simp [leftWord,rightWord]

 

theorem normalized_factorization_exists (hsk : MalcevCharacters.SecondKind c)
    (hΓ : ∀ x : G,x∈Γ ↔ ∀ i,∃ z : ℤ,c.coord x i=z)
    (hK0 : K.level 0=⊤) (hK1 : K.level 1=⊤) (hKs : K.level (s+1)=⊥)
    (r : ℕ → ℕ) (hr : ∀ k,r k≤n)
    (hadapt : ∀ k (x : G),x∈K.level k ↔ ∀ i : Fin n,i.val<r k → c.coord x i=0)
    (hP : ∀ N,P N∈polynomials K 0) (hP0 : ∀ N,P N 0=1)
    (hL : ∀ N,0<L N) :
    ∃ S : State c Γ s K P L,S.Irrational := by
  classical
  have hb (N : ℕ) : ∃ b : ℕ → G,
      (∀ i<s+1,b i∈K.level i) ∧ P N=word b (s+1) := by
    simpa using exists_taylor (H:=K) (k:=0) (d:=s+1) (by simpa using hKs) (hP N)
  choose b hb hword using hb
  let a : ℕ → ∀ k : ℕ,K.level k:=fun N k=>
    if hk : k<s+1 then ⟨b N k,hb N k hk⟩ else 1
  have haword (N : ℕ) : word (fun k=>(a N k).val) (s+1)=P N := by
    rw [hword]
    apply word_congr
    intro k hk
    dsimp only [a]
    rw [dite_eq_left hk]
  have ha0 (N : ℕ) : (a N 0).val=1 := by
    rw [← word_zero (fun k=>(a N k).val) s,haword,hP0]
  obtain ⟨S,hirr⟩:=(initialState (L:=L) hsk hΓ hK0 hK1 hKs r hr hadapt a ha0).exists_irrational_state hL
  have he : (fun N=>word (fun k=>(a N k).val) (s+1))=P:=funext haword
  exact he ▸ ⟨S,hirr⟩

end AllLevelStates
end
 
end

section
 

 

noncomputable section
open scoped Topology
open Filter
universe u
namespace AllLevelRemovals
open RationalLattice RationalFactorPeriods
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {L : ℕ → ℝ}

omit [IsTopologicalGroup G] in
lemma rightWord_ordered [IsTopologicalGroup G] (W : List (Removal c L s)) (N : ℕ) (z : ℤ) :
    rightWord W N z=orderedWord
      (fun i : Fin W.reverse.length =>
        (W.reverse.get i).flow (Multiplicative.ofAdd 1) ^ (W.reverse.get i).integer N)
      (fun i=>(W.reverse.get i).degree) z := by
  unfold rightWord orderedWord
  simp only [← zpow_mul]
  have hl:=List.map_get_finRange W.reverse
  conv_lhs => rw [← hl, List.map_map]
  rfl

 

theorem rightWord_residues [PreconnectedSpace G] [LocallyCompactSpace G] [T2Space G]
    (Γ : Subgroup G) [DiscreteTopology Γ]
    (hΓrat : Γ≤rationalSubgroup c)
    (C : Set G) (hC : IsCompact C) (hreps : ∀ g : G,∃ x∈C,x⁻¹*g∈Γ)
    (W : List (Removal c L s)) :
    ∃ (φ : ℕ → ℕ) (T : ℕ) (σ : Fin T → G),StrictMono φ ∧ 0<T ∧
      (∀ r,IsRational c (σ r)) ∧ ∀ N z,∃ r : Fin T,
        (r.val:ℤ)=z%(T:ℤ) ∧
        (QuotientGroup.mk (rightWord W (φ N) z) : G⧸Γ)=QuotientGroup.mk (σ r) := by
  obtain ⟨φ,T,σ,hφ,hT,hσ,he⟩:=rational_right_factors c Γ hΓrat C hC hreps
    (fun i : Fin W.reverse.length=>(W.reverse.get i).flow (Multiplicative.ofAdd 1))
    (fun i=>(W.reverse.get i).rational_unit)
    (fun N i=>(W.reverse.get i).integer N)
    (fun i=>(W.reverse.get i).degree) s (fun i=>(W.reverse.get i).degree_le)
  refine ⟨φ,T,σ,hφ,hT,hσ,?_⟩
  intro N z
  rw [rightWord_ordered]
  exact he N z

end AllLevelRemovals
namespace AllLevelStates
open RationalLattice AllLevelDomains AllLevelRemovals CubeFaces NilpotentTaylor
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
namespace State

 

def reindex (S : State c Γ s K P L) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    State c Γ s K P L where
  domain := S.domain
  subseq := S.subseq∘φ
  strictmono := S.strictmono.comp hφ
  coeff := fun N=>S.coeff (φ N)
  zero := fun N=>S.zero (φ N)
  level_image := S.level_image
  removals := S.removals.map (fun w=>w.reindex φ hφ)
  realization := by
    intro N z
    rw [leftWord_reindex,rightWord_reindex]
    exact S.realization (φ N) z

lemma irrational_reindex (S : State c Γ s K P L) (hirr : S.Irrational)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : (S.reindex φ hφ).Irrational := by
  intro j hj hjs χ hne hcont hrat hnext hbr
  exact (hirr j hj hjs χ hne hcont hrat hnext hbr).comp hφ.tendsto_atTop

 

theorem exists_irrational_fixed_residues
    [PreconnectedSpace G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ]
    (hΓrat : Γ≤rationalSubgroup c)
    (C : Set G) (hC : IsCompact C) (hreps : ∀ g : G,∃ x∈C,x⁻¹*g∈Γ)
    (S : State c Γ s K P L) (hirr : S.Irrational) :
    ∃ (T : State c Γ s K P L) (d : ℕ) (σ : Fin d → G),
      T.Irrational ∧ 0<d ∧ (∀ r,IsRational c (σ r)) ∧
      ∀ N z,∃ r : Fin d,(r.val:ℤ)=z%(d:ℤ) ∧
        (QuotientGroup.mk (rightWord T.removals N z) : G⧸Γ)=QuotientGroup.mk (σ r) := by
  obtain ⟨φ,d,σ,hφ,hd,hσ,he⟩:=rightWord_residues Γ hΓrat C hC hreps S.removals
  refine ⟨S.reindex φ hφ,d,σ,S.irrational_reindex hirr φ hφ,hd,hσ,?_⟩
  intro N z
  change ∃ r : Fin d,(r.val:ℤ)=z%(d:ℤ) ∧
    (QuotientGroup.mk (rightWord (S.removals.map (fun w=>w.reindex φ hφ)) N z) : G⧸Γ)=
      QuotientGroup.mk (σ r)
  rw [rightWord_reindex]
  exact he N z

end State
end AllLevelStates
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter
namespace ParametricSmooth
open _root_.Polynomial _root_.OAI.Polynomial
variable {σ : Type*}

def family (p : Polynomial (MvPolynomial σ ℝ)) (t : σ → ℝ) : Polynomial ℝ :=
  p.map (MvPolynomial.eval t)

def IsPolynomial (f : (σ → ℝ) → ℝ → ℝ) : Prop :=
  ∃ p : Polynomial (MvPolynomial σ ℝ),∀ t x,(family p t).eval x=f t x

lemma constant (a : ℝ) : IsPolynomial (fun (_ : σ → ℝ) _=>a) :=
  ⟨C (MvPolynomial.C a),by intro t x; simp [family]⟩
lemma coordinate : IsPolynomial (fun (_ : σ → ℝ) x=>x) :=
  ⟨X,by intro t x; simp [family]⟩
lemma parameter (i : σ) : IsPolynomial (fun (t : σ → ℝ) _=>t i) :=
  ⟨C (MvPolynomial.X i),by intro t x; simp [family]⟩
lemma add {f g : (σ → ℝ) → ℝ → ℝ} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun t x=>f t x+g t x) := by
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hg
  refine ⟨p+q,?_⟩
  intro t x
  change ((p+q).map _).eval x=_
  rw [Polynomial.map_add,eval_add]
  exact congrArg₂ (·+·) (hp t x) (hq t x)
lemma mul {f g : (σ → ℝ) → ℝ → ℝ} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun t x=>f t x*g t x) := by
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hg
  refine ⟨p*q,?_⟩
  intro t x
  change ((p*q).map _).eval x=_
  rw [Polynomial.map_mul,eval_mul]
  exact congrArg₂ (·*·) (hp t x) (hq t x)
lemma neg {f : (σ → ℝ) → ℝ → ℝ} (hf : IsPolynomial f) :
    IsPolynomial (fun t x=>-f t x) := by
  simpa using mul (constant (-1)) hf
lemma sub {f g : (σ → ℝ) → ℝ → ℝ} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun t x=>f t x-g t x) := by simpa [sub_eq_add_neg] using add hf (neg hg)
lemma pow {f : (σ → ℝ) → ℝ → ℝ} (hf : IsPolynomial f) (k : ℕ) :
    IsPolynomial (fun t x=>(f t x)^k) := by
  induction k with
  | zero => simpa using constant (σ:=σ) 1
  | succ k ih => simpa [pow_succ] using mul ih hf
lemma finite_sum {ι : Type*} (S : Finset ι) {f : ι → (σ → ℝ) → ℝ → ℝ}
    (hf : ∀ i∈S,IsPolynomial (f i)) : IsPolynomial (fun t x=>∑ i∈S,f i t x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using constant (σ:=σ) 0
  | @insert i S hi ih =>
    simpa [Finset.sum_insert hi] using add (hf i (by simp)) (ih (fun j hj=>hf j (by simp [hj])))
lemma finite_prod {ι : Type*} (S : Finset ι) {f : ι → (σ → ℝ) → ℝ → ℝ}
    (hf : ∀ i∈S,IsPolynomial (f i)) : IsPolynomial (fun t x=>∏ i∈S,f i t x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using constant (σ:=σ) 1
  | @insert i S hi ih =>
    simpa [Finset.prod_insert hi] using mul (hf i (by simp)) (ih (fun j hj=>hf j (by simp [hj])))
lemma polynomial_eval (p : Polynomial ℝ) {f : (σ → ℝ) → ℝ → ℝ} (hf : IsPolynomial f) :
    IsPolynomial (fun t x=>p.eval (f t x)) := by
  simp only [Polynomial.eval_eq_sum_range]
  exact finite_sum _ (fun i _=>mul (constant _) (pow hf i))
lemma mvpolynomial_eval {ι : Type*} (p : MvPolynomial ι ℚ)
    {f : ι → (σ → ℝ) → ℝ → ℝ} (hf : ∀ i,IsPolynomial (f i)) :
    IsPolynomial (fun t x=>MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i=>f i t x) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using constant (σ:=σ) (a:ℝ)
  | add p q hp hq => simpa using add hp hq
  | mul_X p i hp => simpa using mul hp (hf i)

lemma rename_parameters {τ : Type*} {f : (σ → ℝ) → ℝ → ℝ}
    (hf : IsPolynomial f) (e : σ → τ) : IsPolynomial (fun t x=>f (t∘e) x) := by
  obtain ⟨p,hp⟩:=hf
  refine ⟨p.map (MvPolynomial.rename e).toRingHom,?_⟩
  intro t x
  have he : (MvPolynomial.eval t).comp (MvPolynomial.rename e).toRingHom=
      MvPolynomial.eval (t∘e) := by
    apply RingHom.ext
    intro P
    exact MvPolynomial.eval_rename e t P
  simp only [family,Polynomial.map_map,he]
  exact hp (t∘e) x

lemma continuous_eval (p : Polynomial (MvPolynomial σ ℝ)) :
    Continuous (fun z : (σ → ℝ) × ℝ=>(family p z.1).eval z.2) := by
  simp only [family,eval_map,eval₂_eq_sum_range]
  apply continuous_finsetSum
  intro i _
  exact ((MvPolynomial.continuous_eval (p.coeff i)).comp continuous_fst).mul (continuous_snd.pow i)

lemma derivative_family (p : Polynomial (MvPolynomial σ ℝ)) (t : σ → ℝ) (k : ℕ) :
    derivative^[k] (family p t)=family (derivative^[k] p) t := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
    rw [show derivative (family p t)=family p.derivative t from derivative_map p _]
    exact ih p.derivative

 

theorem compact_derivative_limit [Fintype σ] {ι : Type*} {l : Filter ι}
    {f : (σ → ℝ) → ℝ → ℝ} (hf : IsPolynomial f)
    {a : ι → σ → ℝ} {a₀ : σ → ℝ} (ha : Tendsto a l (𝓝 a₀))
    (k : ℕ) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N=>iteratedDeriv k (f (a N))) (iteratedDeriv k (f a₀)) l K := by
  obtain ⟨p,hp⟩:=hf
  have he (t : σ → ℝ) : f t=fun x=>(family p t).eval x:=funext (fun x=>(hp t x).symm)
  simp_rw [he,SmoothBinomial.iteratedDeriv_eval,derivative_family]
  let : CompactSpace K:=isCompact_iff_compactSpace.mp hK
  let F : (σ → ℝ) → K → ℝ:=fun t x=>(family (derivative^[k] p) t).eval x.val
  have hF : Continuous (Function.uncurry F):=
    (continuous_eval (derivative^[k] p)).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hu:=hF.tendstoUniformly F a₀
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  intro u hu'
  exact ha.eventually (hu u hu')

 

theorem compact_derivative_bound {f : (σ → ℝ) → ℝ → ℝ} (hf : IsPolynomial f)
    {a : ℕ → σ → ℝ} {a₀ : σ → ℝ} (ha : Tendsto a atTop (𝓝 a₀))
    (k : ℕ) (K : Set ℝ) (hK : IsCompact K) :
    ∃ B>0,∀ N x,x∈K → |iteratedDeriv k (f (a N)) x|≤B := by
  obtain ⟨p,hp⟩:=hf
  have he (t : σ → ℝ) : f t=fun x=>(family p t).eval x:=funext (fun x=>(hp t x).symm)
  obtain ⟨M,hM⟩:=(ha.isCompact_insert_range.prod hK).exists_bound_of_continuousOn
    (continuous_eval (derivative^[k] p)).continuousOn
  refine ⟨max M 0+1,by positivity,?_⟩
  intro N x hx
  rw [he,SmoothBinomial.iteratedDeriv_eval,derivative_family]
  have hb:=hM (a N,x) ⟨Set.mem_insert_of_mem _ (Set.mem_range_self N),hx⟩
  have hb' : |(family (derivative^[k] p) (a N)).eval x|≤M:=by
    simpa only [Real.norm_eq_abs] using hb
  exact hb'.trans (by linarith [le_max_left M 0])

end ParametricSmooth

end
end
end
end

end OAI
