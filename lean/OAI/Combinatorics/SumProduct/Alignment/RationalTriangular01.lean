import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel05
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators Topology
open Filter
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology commutatorElement
open Filter Topology
universe u
namespace AllLevelFactorization
open RationalLattice CubeFaces CubePolynomials NilpotentTaylor
open AllLevelDomains AllLevelRemovals AllLevelStates
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (Γ : Subgroup G) (s : ℕ)
variable (K : Filtration G) (P : ℕ → ℤ → G) (L : ℕ → ℝ)

 

structure Factorization where
  normalized : ℕ → ℤ → G
  constantPart : ℕ → G
  normal_quotient : ∀ N z,(QuotientGroup.mk (P N z) : G⧸Γ)=
    QuotientGroup.mk (constantPart N*normalized N z)
  state : State c Γ s K normalized L
  irrational : state.Irrational
  period : ℕ
  period_pos : 0<period
  residue : Fin period → G
  residue_rational : ∀ r,IsRational c (residue r)
  right_residue : ∀ N z,∃ r : Fin period,(r.val:ℤ)=z%(period:ℤ) ∧
    (QuotientGroup.mk (rightWord state.removals N z) : G⧸Γ)=QuotientGroup.mk (residue r)
  prefixLimit : G
  prefix_tendsto : Tendsto (constantPart∘state.subseq) atTop (𝓝 prefixLimit)

variable {c Γ s K P L}

 

theorem factorization_exists (hsk : MalcevCharacters.SecondKind c)
    (hΓ : ∀ x : G,x∈Γ ↔ ∀ i,∃ z : ℤ,c.coord x i=z)
    (hK0 : K.level 0=⊤) (hK1 : K.level 1=⊤) (hKs : K.level (s+1)=⊥)
    (r : ℕ → ℕ) (hr : ∀ k,r k≤n)
    (hadapt : ∀ k (x : G),x∈K.level k ↔ ∀ i : Fin n,i.val<r k → c.coord x i=0)
    (hP : ∀ N,P N∈polynomials K 0) (hL : ∀ N,0<L N) :
    Nonempty (Factorization c Γ s K P L) := by
  classical
  let : ConnectedSpace G:=coordinates_connected c
  let : LocallyCompactSpace G:=coordinates_locallyCompact c
  let : SecondCountableTopology G:=coordinates_secondCountable c
  let : T2Space G:=c.coord.symm.t2Space
  let : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  obtain ⟨C,hC,hreps⟩:=compact_reps_of_integerCoordinates c Γ hΓ
  choose a ha hγ using fun N=>hreps (P N 0)
  let γ : ℕ → G:=fun N=>(a N)⁻¹*P N 0
  let R : ℕ → ℤ → G:=fun N z=>(a N)⁻¹*P N z*(γ N)⁻¹
  have hR (N : ℕ) : R N∈polynomials K 0 := by
    apply (polynomials K 0).mul_mem
    · exact (polynomials K 0).mul_mem (const_mem (by simp [hK0])) (hP N)
    · exact const_mem (by simp [hK0])
  have hR0 (N : ℕ) : R N 0=1 := by simp [R,γ]
  have hq (N : ℕ) (z : ℤ) : (QuotientGroup.mk (P N z) : G⧸Γ)=
      QuotientGroup.mk (a N*R N z) := by
    have he : a N*R N z=P N z*(γ N)⁻¹:=by simp [R,← mul_assoc]
    rw [he,QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem (hγ N))]
  obtain ⟨S,hS⟩:=normalized_factorization_exists hsk hΓ hK0 hK1 hKs r hr hadapt hR hR0 hL
  obtain ⟨T,d,σ,hT,hd,hσ,he⟩:=S.exists_irrational_fixed_residues
    (integerCoordinates_rational c Γ hΓ) C hC hreps hS
  obtain ⟨a₀,_,φ,hφ,ht⟩:=hC.tendsto_subseq (fun N=>ha (T.subseq N))
  refine ⟨{ normalized := R
            constantPart := a
            normal_quotient := hq
            state := T.reindex φ hφ
            irrational := T.irrational_reindex hT φ hφ
            period := d
            period_pos := hd
            residue := σ
            residue_rational := hσ
            right_residue := ?_
            prefixLimit := a₀
            prefix_tendsto := ht }⟩
  intro N z
  change ∃ t : Fin d,(t.val:ℤ)=z%(d:ℤ) ∧
    (QuotientGroup.mk (rightWord (T.removals.map (fun w=>w.reindex φ hφ)) N z) : G⧸Γ)=
      QuotientGroup.mk (σ t)
  rw [rightWord_reindex]
  exact he (φ N) z

namespace Factorization
variable (F : Factorization c Γ s K P L)

def smoothPart (N : ℕ) (b : ℝ) : G :=
  F.constantPart (F.state.subseq N)*smoothWord F.state.removals N b

def smoothLimit (β : ℝ) : G :=
  F.prefixLimit*AllLevelRemovals.smoothLimit F.state.removals β

def structuredPart (N : ℕ) (z : ℤ) : F.state.domain.Carrier :=
  word (fun k=>(F.state.coeff N k).val) (s+1) z

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma quotient_mul_congr [TopologicalSpace G] [IsTopologicalGroup G] (a b g : G)
    (h : (QuotientGroup.mk a : G⧸Γ)=QuotientGroup.mk b) :
    (QuotientGroup.mk (g*a) : G⧸Γ)=QuotientGroup.mk (g*b) := by
  apply QuotientGroup.eq.mpr
  have hm:=QuotientGroup.eq.mp h
  simpa [mul_inv_rev,mul_assoc] using hm

 
theorem realization (N : ℕ) (z : ℤ) :
    ∃ r : Fin F.period,(r.val:ℤ)=z%(F.period:ℤ) ∧
    (QuotientGroup.mk (P (F.state.subseq N) z) : G⧸Γ)=
      QuotientGroup.mk (F.smoothPart N z*F.state.domain.embed (F.structuredPart N z)*
        F.residue r) := by
  obtain ⟨r,hr,he⟩:=F.right_residue N z
  refine ⟨r,hr,?_⟩
  rw [F.normal_quotient,F.state.realization]
  have hw : smoothWord F.state.removals N (z:ℝ)=leftWord F.state.removals N z:=
    smoothWord_integer _ _ _
  dsimp only [smoothPart,structuredPart]
  rw [hw]
  simpa only [mul_assoc] using quotient_mul_congr
    (rightWord F.state.removals N z) (F.residue r)
    (F.constantPart (F.state.subseq N)*leftWord F.state.removals N z*
      F.state.domain.embed (word (fun k=>(F.state.coeff N k).val) (s+1) z)) he

 

theorem smooth_limit (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
    (k : ℕ) (i : Fin n) (A : Set ℝ) (hA : IsCompact A) :
    TendstoUniformlyOn (fun N=>iteratedDeriv k
      (fun β=>c.coord (F.smoothPart N (L (F.state.subseq N)*β)) i))
      (iteratedDeriv k (fun β=>c.coord (F.smoothLimit β) i)) atTop A := by
  exact prefix_smoothWord_limit F.state.removals (fun N=>hL _)
    (ht.comp F.state.strictmono.tendsto_atTop) F.prefix_tendsto k i A hA

theorem smooth_bounds (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
    (k : ℕ) (i : Fin n) (A : Set ℝ) (hA : IsCompact A) :
    ∃ B>0,∀ N β,β∈A →
      |iteratedDeriv k (fun β=>c.coord (F.smoothPart N (L (F.state.subseq N)*β)) i) β|≤B := by
  exact prefix_smoothWord_bounds F.state.removals (fun N=>hL _)
    (ht.comp F.state.strictmono.tendsto_atTop) F.prefix_tendsto k i A hA

theorem limit_smooth (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun β=>c.coord (F.smoothLimit β) i) :=
  prefix_smoothLimit_smooth F.state.removals F.prefixLimit i

end Factorization

end AllLevelFactorization
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalLattice
open MalcevCharacters RationalLevelFlow
variable {G H : Type*} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable {m n : ℕ} (c : RealCoordinates G m) (d : RealCoordinates H n)

omit [IsTopologicalGroup G] in
lemma polynomialMap_realPower [IsTopologicalGroup G] {σ : Type*} {g : G} (hg : IsRational c g)
    {f : (σ → ℝ) → ℝ} (hf : RationalPolynomialMap.IsPolynomial f) :
    IsPolynomialMap c (fun x=>realPower c g (f x)) := by
  intro j
  obtain ⟨p,hp⟩:=powerPolynomial_rational c hg j
  simpa only [realPower_coord,hp,Polynomial.eval_map] using
    RationalPolynomialMap.polynomial_eval p hf

omit [IsTopologicalGroup G] in
lemma polynomialMap_list_prod [IsTopologicalGroup G] {σ : Type*} (V : List ((σ → ℝ) → G))
    (hV : ∀ f∈V,IsPolynomialMap c f) :
    IsPolynomialMap c (fun x=>(V.map (fun f=>f x)).prod) := by
  induction V with
  | nil => simpa using polynomialMap_one c
  | cons f V ih =>
    simpa using polynomialMap_mul c (hV f (by simp)) (ih (fun f hf=>hV f (by simp [hf])))

omit [IsTopologicalGroup H] in
lemma axis_rational [IsTopologicalGroup H] (i : Fin n) (t : ℚ) : IsRational d (axis d i t) := by
  classical
  intro j
  refine ⟨if j=i then t else 0,?_⟩
  simp only [coord_axis,Pi.single_apply]
  split_ifs <;> simp

 

theorem rationalHom_polynomial (hsk : SecondKind d) (F : H →* G)
    (hF : Continuous F) (hrat : ∀ x,IsRational d x → IsRational c (F x)) :
    IsPolynomialMap c (fun x : Fin n → ℝ=>F (d.coord.symm x)) := by
  let A (i : Fin n) : Multiplicative ℝ →* H :=
    { toFun := fun t=>axis d i t.toAdd
      map_one' := axis_zero d i
      map_mul' := fun t u=>hsk.axis_add i t.toAdd u.toAdd }
  have he (i : Fin n) (t : ℝ) : F (axis d i t)=realPower c (F (axis d i 1)) t :=
    continuous_flow_eq_realPower c (F.comp (A i))
      (hF.comp ((axis_continuous d i).comp continuous_toAdd)) t
  have hp (i : Fin n) : IsPolynomialMap c (fun x : Fin n → ℝ=>F (axis d i (x i))) := by
    have hfun : (fun x : Fin n → ℝ=>F (axis d i (x i))) =
        (fun x=>realPower c (F (axis d i 1)) (x i)) := funext (fun x=>he i (x i))
    rw [hfun]
    simpa only [Rat.cast_one] using polynomialMap_realPower c (hrat _ (axis_rational d i 1))
      (RationalPolynomialMap.coordinate i)
  have hprod:=polynomialMap_list_prod c (List.ofFn (fun i : Fin n=>
    (fun x : Fin n → ℝ=>F (axis d i (x i))))) (by
      intro f hf
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hf
      exact hp i)
  have hw (x : Fin n → ℝ) : F (d.coord.symm x)=
      ((List.ofFn (fun i : Fin n=>(fun x : Fin n → ℝ=>F (axis d i (x i))))).map
        (fun f=>f x)).prod := by
    conv_lhs => rw [hsk.ordered (d.coord.symm x)]
    rw [map_list_prod,List.map_ofFn,List.map_ofFn]
    simp only [Homeomorph.apply_symm_apply,Function.comp_def]
  simpa only [← hw] using hprod

end RationalLattice

end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalTriangularChange
open MvPolynomial

def forward {n : ℕ} (p : (i : Fin n) → MvPolynomial (Fin i.val) ℚ)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i + eval₂ (algebraMap ℚ ℝ) (fun j=>x ⟨j.val,lt_trans j.isLt i.isLt⟩) (p i)

def inverse : {n : ℕ} → ((i : Fin n) → MvPolynomial (Fin i.val) ℚ) →
    (Fin n → ℝ) → (Fin n → ℝ)
  | 0, _, _ => Fin.elim0
  | n+1, p, y =>
    let x := inverse (fun i : Fin n=>p i.castSucc) (fun i=>y i.castSucc)
    Fin.snoc x (y (Fin.last n)-eval₂ (algebraMap ℚ ℝ) x (p (Fin.last n)))

lemma inverse_castSucc {n : ℕ} (p : (i : Fin (n+1)) → MvPolynomial (Fin i.val) ℚ)
    (y : Fin (n+1) → ℝ) (i : Fin n) :
    inverse p y i.castSucc=inverse (fun i : Fin n=>p i.castSucc) (fun i=>y i.castSucc) i := by
  simp [inverse]

lemma inverse_last {n : ℕ} (p : (i : Fin (n+1)) → MvPolynomial (Fin i.val) ℚ)
    (y : Fin (n+1) → ℝ) :
    inverse p y (Fin.last n)=y (Fin.last n)-eval₂ (algebraMap ℚ ℝ)
      (inverse (fun i : Fin n=>p i.castSucc) (fun i=>y i.castSucc)) (p (Fin.last n)) := by
  simp [inverse]

lemma forward_inverse {n : ℕ} (p : (i : Fin n) → MvPolynomial (Fin i.val) ℚ)
    (y : Fin n → ℝ) : forward p (inverse p y)=y := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · unfold forward
      rw [inverse_last]
      have hfun : (fun j : Fin (Fin.last n).val=>inverse p y ⟨j.val,lt_trans j.isLt (Fin.last n).isLt⟩)=
          inverse (fun i : Fin n=>p i.castSucc) (fun i=>y i.castSucc) := by
        funext j
        exact inverse_castSucc p y j
      rw [hfun]
      ring
    · have h:=congrFun (ih (fun i : Fin n=>p i.castSucc) (fun i=>y i.castSucc)) i
      have hfun : (fun j : Fin i.val=>inverse p y ⟨j.val,lt_trans j.isLt i.castSucc.isLt⟩)=
          (fun j : Fin i.val=>inverse (fun i : Fin n=>p i.castSucc)
            (fun i=>y i.castSucc) ⟨j.val,lt_trans j.isLt i.isLt⟩) := by
        funext j
        exact inverse_castSucc p y ⟨j.val,lt_trans j.isLt i.isLt⟩
      unfold forward
      rw [inverse_castSucc]
      exact (congrArg (fun f=>inverse (fun i : Fin n=>p i.castSucc)
        (fun i=>y i.castSucc) i + eval₂ (algebraMap ℚ ℝ) f (p i.castSucc)) hfun).trans h

lemma forward_injective {n : ℕ} (p : (i : Fin n) → MvPolynomial (Fin i.val) ℚ) :
    Function.Injective (forward p) := by
  intro x y h
  have H : ∀ k,∀ hk : k<n,x ⟨k,hk⟩=y ⟨k,hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hh:=congrFun h ⟨k,hk⟩
      have he : (fun j : Fin k=>x ⟨j.val,lt_trans j.isLt hk⟩)=
          (fun j : Fin k=>y ⟨j.val,lt_trans j.isLt hk⟩) := funext fun j=>ih j.val j.isLt _
      simp only [forward,he] at hh
      exact add_right_cancel hh
  funext i
  exact H i.val i.isLt

lemma inverse_forward {n : ℕ} (p : (i : Fin n) → MvPolynomial (Fin i.val) ℚ)
    (x : Fin n → ℝ) : inverse p (forward p x)=x :=
  forward_injective p (forward_inverse p (forward p x))

lemma forward_polynomial {n : ℕ} (p : (i : Fin n) → MvPolynomial (Fin i.val) ℚ)
    (i : Fin n) : RationalPolynomialMap.IsPolynomial (fun x=>forward p x i) := by
  apply RationalPolynomialMap.add (RationalPolynomialMap.coordinate i)
  exact RationalPolynomialMap.eval (fun j=>RationalPolynomialMap.coordinate _) (p i)

lemma inverse_polynomial {n : ℕ} (p : (i : Fin n) → MvPolynomial (Fin i.val) ℚ)
    (i : Fin n) : RationalPolynomialMap.IsPolynomial (fun x=>inverse p x i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i=>?_) i
    · have hx (j : Fin n) : RationalPolynomialMap.IsPolynomial
          (fun y : Fin (n+1) → ℝ=>inverse (fun i : Fin n=>p i.castSucc) (fun i=>y i.castSucc) j) :=
        RationalPolynomialMap.comp (ih _ j) (fun i=>RationalPolynomialMap.coordinate i.castSucc)
      simpa only [inverse_last] using RationalPolynomialMap.sub
        (RationalPolynomialMap.coordinate (Fin.last n)) (RationalPolynomialMap.eval hx (p (Fin.last n)))
    · simpa only [inverse_castSucc] using RationalPolynomialMap.comp
        (ih (fun i : Fin n=>p i.castSucc) i) (fun i : Fin n=>RationalPolynomialMap.coordinate i.castSucc)

lemma polynomial_continuous {σ : Type*} {f : (σ → ℝ) → ℝ}
    (hf : RationalPolynomialMap.IsPolynomial f) : Continuous f := by
  obtain ⟨p,hp⟩:=hf
  have h:=MvPolynomial.continuous_eval (MvPolynomial.map (algebraMap ℚ ℝ) p)
  simpa only [MvPolynomial.eval_map, ← hp] using h

def homeomorph {n : ℕ} (p : (i : Fin n) → MvPolynomial (Fin i.val) ℚ) :
    (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toFun:=forward p
  invFun:=inverse p
  left_inv:=inverse_forward p
  right_inv:=forward_inverse p
  continuous_toFun:=continuous_pi (fun i=>polynomial_continuous (forward_polynomial p i))
  continuous_invFun:=continuous_pi (fun i=>polynomial_continuous (inverse_polynomial p i))

end RationalTriangularChange

end
end
end
end

end OAI
