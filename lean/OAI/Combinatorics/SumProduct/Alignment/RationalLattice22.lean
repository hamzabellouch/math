import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.EmbeddedCube01
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays01
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice21
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalLattice.JointArrays
open MalcevCharacters CubePolynomials
variable {ι : Type} [Fintype ι] (G : ι → Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n q : ι → ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i) → ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j) (hmono : ∀ i,Monotone (w i))

abbrev Component (i : ι) : Type := PolynomialArrays.group (q:=q i) (c i) (hsk i) (A i) (w i) (hA i)
abbrev Carrier := ∀ i,Component G n q c hsk A w hA i
abbrev dimension (i : ι) := Fintype.card (PolynomialArrays.Index (w i) (q i))
abbrev componentWeight (i : ι) := PolynomialArrays.orderedWeight (q:=q i) (w i)
abbrev filtration : CubeFaces.Filtration (Carrier G n q c hsk A w hA) := FiniteProducts.filtration (Component G n q c hsk A w hA)
  (fun i=>PolynomialArrays.filtration (q:=q i) (c i) (hsk i) (A i) (w i) (hA i))
variable (Γ : ∀ i,Subgroup (G i))
variable (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z)
abbrev lattice : Subgroup (Carrier G n q c hsk A w hA) := FiniteProducts.lattice (Component G n q c hsk A w hA)
  (fun i=>PolynomialArrays.lattice (q:=q i) (c i) (hsk i) (A i) (w i) (hA i) (Γ i))
abbrev jointWeight := FiniteProducts.orderedWeight (dimension n q w) (componentWeight n q w)

include hw hmono hΓ in
lemma covered_geometry : ∃ e : RealCoordinates (Carrier G n q c hsk A w hA)
    (Fintype.card (FiniteProducts.Index (dimension n q w))),
    SecondKind e ∧ Nonempty (CoveredLattice e (lattice G n q c hsk A w hA Γ)) ∧
      (∀ k f,f∈(filtration G n q c hsk A w hA).level k ↔
        ∀ j,jointWeight n q w j<k → e.coord f j=0) ∧
      (∀ f,IsRational e f → ∀ i (u : Fin (q i) → ℤ),
        IsRational (c i) ((f i).val (fun j=>(u j:ℝ)))) := by
  classical
  have hi (i : ι):=PolynomialArrays.covered_geometry (q:=q i)
    (c i) (hsk i) (A i) (w i) (hA i) (hw i) (hmono i) (Γ i) (hΓ i)
  choose d hds hdB hda hdr using hi
  let B (i : ι):=Classical.choice (hdB i)
  let K:=Component G n q c hsk A w hA
  let T i:=PolynomialArrays.filtration (q:=q i) (c i) (hsk i) (A i) (w i) (hA i)
  let v i:=PolynomialArrays.orderedWeight (q:=q i) (w i)
  have hv (i : ι) (j : Fin (dimension n q w i)) : 0<v i j:=
    PolynomialArrays.orderedWeight_pos (w i) (hw i) j
  have hm (i : ι) : Monotone (v i):=PolynomialArrays.orderedWeight_monotone (w i)
  obtain ⟨e,he,hB,ha,hr⟩:=FiniteProducts.covered_geometry K (dimension n q w) d hds T v hv hm hda
    (fun i=>PolynomialArrays.lattice (q:=q i) (c i) (hsk i) (A i) (w i) (hA i) (Γ i)) B
  refine ⟨e,he,hB,ha,?_⟩
  intro f hf i u
  have hd:=FiniteProducts.projection_rational K (dimension n q w) d hds T v hv hda f (hr f |>.mp hf) i
  have hc:=(hdr i (f i)).mp hd
  exact PolynomialArrays.evaluate_rational (c i) (hsk i) (A i) (w i) (hA i) (hw i) u (f i) hc

lemma filtration_top (k : ℕ) (hk : ∀ i,(A i).level k=⊤) :
    (filtration G n q c hsk A w hA).level k=⊤ :=
  FiniteProducts.filtration_top _ _ k (fun i=>PolynomialArrays.filtration_top
    (c i) (hsk i) (A i) (w i) (hA i) k (hk i))
lemma filtration_terminal (s : ℕ) (hs : ∀ i,(A i).level (s+1)=⊥) :
    (filtration G n q c hsk A w hA).level (s+1)=⊥ :=
  FiniteProducts.filtration_terminal _ _ s (fun i=>PolynomialArrays.filtration_terminal
    (c i) (hsk i) (A i) (w i) (hA i) s (hs i))

def orbit (g x : ∀ i,G i) (t : ι → ℤ) (b : ι → ℝ) (v : ∀ i,Fin (q i) → ℝ) (z : ℤ) :
    Carrier G n q c hsk A w hA:=
  fun i=>PolynomialArrays.sourceOrbit (c i) (hsk i) (A i) (w i) (hA i) (hw i)
    (g i) (x i) (t i) (b i) (v i) z

omit [Fintype ι] in
lemma orbit_apply [Fintype ι] (g x : ∀ i,G i) (t : ι → ℤ) (b : ι → ℝ) (v : ∀ i,Fin (q i) → ℝ)
    (z : ℤ) (i : ι) (u : Fin (q i) → ℝ) :
    ((orbit G n q c hsk A w hA hw g x t b v z) i).val u=
      realPower (c i) (g i) (b i+(t i:ℝ)*z+∑ j,v i j*u j)*x i :=
  PolynomialArrays.sourceOrbit_apply (c i) (hsk i) (A i) (w i) (hA i) (hw i)
    (g i) (x i) (t i) (b i) (v i) u z

lemma orbit_polynomial (h0 : ∀ i,(A i).level 0=⊤) (h1 : ∀ i,(A i).level 1=⊤)
    (g x : ∀ i,G i) (t : ι → ℤ) (b : ι → ℝ) (v : ∀ i,Fin (q i) → ℝ) :
    orbit G n q c hsk A w hA hw g x t b v∈polynomials (filtration G n q c hsk A w hA) 0 := by
  let a : Carrier G n q c hsk A w hA:=fun i=>PolynomialArrays.constantElement
    (q:=q i) (c i) (hsk i) (A i) (w i) (hA i) (g i^t i)
  let x₀ : Carrier G n q c hsk A w hA:=fun i=>PolynomialArrays.sourceElement
    (c i) (hsk i) (A i) (w i) (hA i) (hw i) (g i) (x i) (b i) (v i)
  have hp:=power_polynomial_mem 1 0 a (by
    rw [Nat.add_zero,filtration_top G n q c hsk A w hA 1 h1]
    trivial) Polynomial.X (by simp)
  have hc : (fun _ : ℤ=>x₀)∈polynomials (filtration G n q c hsk A w hA) 0:=const_mem (by
    rw [filtration_top G n q c hsk A w hA 0 h0]
    trivial)
  have H:=(polynomials (filtration G n q c hsk A w hA) 0).mul_mem hp hc
  simp only [Polynomial.eval_X,Pi.mul_def] at H
  exact H

end RationalLattice.JointArrays
end
 
end

section
 

 

noncomputable section
open scoped Topology
open Filter MeasureTheory
namespace AllLevelFactorization
open RationalLattice CubeFaces MalcevCharacters MalcevWeightedCoordinates
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (Γ : Subgroup G) (B : CoveredLattice c Γ)
variable (s : ℕ) (K : Filtration G) (w : Fin n → ℕ)
variable (hsk : SecondKind c) (hmono : Monotone w)
variable (hK : ∀ k (g : G),g∈K.level k ↔ ∀ i,w i<k → c.coord g i=0)
variable (h0 : K.level 0=⊤) (h1 : K.level 1=⊤) (hs : K.level (s+1)=⊥)
variable (P : ℕ → ℤ → G) (hP : ∀ N,P N∈CubePolynomials.polynomials K 0)
variable (L : ℕ → ℝ) (hL : ∀ N,0<L N)

include hsk hmono hK h0 h1 hs hP hL in
lemma covered_factorization_exists : Nonempty (Factorization c B.small s K P L) := by
  classical
  choose r hr he using fun k=>exists_weight_cutoff w hmono k
  apply factorization_exists hsk B.integer h0 h1 hs r hr _ hP hL
  intro k g
  rw [hK k g]
  exact forall_congr' (fun i=>by rw [he k i])

 

def coveredFactorization : Factorization c B.small s K P L :=
  Classical.choice (covered_factorization_exists c Γ B s K w hsk hmono hK h0 h1 hs P hP L hL)

def coveredResidues (F : Factorization c B.small s K P L) (r : Fin F.period) : F.ResidueCover r :=
  F.residueCover B.integer r

include B in
omit [IsTopologicalGroup G] in
lemma covered_quotient_compact [IsTopologicalGroup G] : CompactSpace (G⧸Γ) := by
  obtain ⟨S,hS,hrep⟩:=compact_reps_of_integerCoordinates c B.small B.integer
  apply CompactGroupProducts.HasCompactReps.quotient_compactSpace
  refine ⟨S,hS,fun _ _=>Subgroup.mem_top _,?_⟩
  intro g _
  obtain ⟨a,ha,hag⟩:=hrep g
  exact ⟨a,ha,B.le hag⟩

end AllLevelFactorization
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalLattice.JointArrays
open MalcevCharacters CubePolynomials
variable {ι : Type} [Fintype ι] (G : ι → Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n q : ι → ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i) → ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j) (hmono : ∀ i,Monotone (w i))
variable (Γ : ∀ i,Subgroup (G i))
variable (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z)
variable (s : ℕ) (h0 : ∀ i,(A i).level 0=⊤) (h1 : ∀ i,(A i).level 1=⊤)
variable (hs : ∀ i,(A i).level (s+1)=⊥)
variable (g x : ℕ → ∀ i,G i) (t : ℕ → ι → ℤ) (b : ℕ → ι → ℝ)
variable (v : ℕ → ∀ i,Fin (q i) → ℝ) (L : ℕ → ℝ) (hL : ∀ N,0<L N)

include hmono hΓ h0 h1 hs hL in
 

lemma factorization_exists :
    ∃ e : RealCoordinates (Carrier G n q c hsk A w hA)
      (Fintype.card (FiniteProducts.Index (dimension n q w))),
    ∃ B : CoveredLattice e (lattice G n q c hsk A w hA Γ),
      SecondKind e ∧
      (∀ k f,f∈(filtration G n q c hsk A w hA).level k ↔
        ∀ j,jointWeight n q w j<k → e.coord f j=0) ∧
      (∀ f,IsRational e f → ∀ i (u : Fin (q i) → ℤ),
        IsRational (c i) ((f i).val (fun j=>(u j:ℝ)))) ∧
      Nonempty (AllLevelFactorization.Factorization e B.small s
        (filtration G n q c hsk A w hA)
        (fun N=>orbit G n q c hsk A w hA hw (g N) (x N) (t N) (b N) (v N)) L) := by
  obtain ⟨e,he,⟨B⟩,ha,hr⟩:=covered_geometry G n q c hsk A w hA hw hmono Γ hΓ
  refine ⟨e,B,he,ha,hr,?_⟩
  apply AllLevelFactorization.covered_factorization_exists e _ B s _ (jointWeight n q w)
    he (FiniteProducts.orderedWeight_monotone _ _) ha
    (filtration_top G n q c hsk A w hA 0 h0)
    (filtration_top G n q c hsk A w hA 1 h1)
    (filtration_terminal G n q c hsk A w hA s hs)
    _ _ L hL
  intro N
  exact orbit_polynomial G n q c hsk A w hA hw h0 h1 (g N) (x N) (t N) (b N) (v N)

end RationalLattice.JointArrays
end
 
end

noncomputable section
open scoped BigOperators
namespace SourceIntegerArrays
open ProductExposureLabels
lemma exponent_column_affine {m q : ℕ} (M : ℕ) (hM : 0<M) (L : ℤ)
    (b : Label m) (tail : Fin m→ℤ) (pstar slot : ℤ) (qval : Fin q→ℤ) (u : ℤ) :
    exponent M L b tail pstar slot (fun _ : Fin 1=>1) (fun _=>u) qval 0=
      exponent M L b tail pstar slot (fun _ : Fin 1=>1) (fun _=>0) qval 0+(∏ j,tail j)*u := by
  simp only [exponent,Pi.zero_apply,one_mul,mul_zero,Finset.sum_const_zero,add_zero]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.zero_add,one_nsmul]
  have he : (∏ j,tail j)*(pstar+(M:ℤ)*u+slot)-rSlot M b slot=
      ((∏ j,tail j)*(pstar+slot)-rSlot M b slot)+(M:ℤ)*((∏ j,tail j)*u) := by ring
  rw [he,Int.add_mul_ediv_left _ _ (by exact_mod_cast (hM.ne'))]
end SourceIntegerArrays
end

noncomputable section
open scoped BigOperators
namespace SourceIntegerArrays
open RationalLattice MalcevCharacters ProductExposureLabels SourceResidueAlignment
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n q m : ι→ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j)
 

def literalJoint (M : ℕ) (L : ℤ) (b : ∀ i,Label (m i)) (tail : ∀ i,Fin (m i)→ℤ)
    (pstar slot : ι→ℤ) (qval : ∀ i,Fin (q i)→ℤ) (g x : ∀ i,G i) (u : ℤ) :
    JointArrays.Carrier G n q c hsk A w hA := fun i=>
  PolynomialArrays.sourceElement (c i) (hsk i) (A i) (w i) (hA i) (hw i) (g i) (x i)
    (exponent M L (b i) (tail i) (pstar i) (slot i) (fun _ : Fin 1=>1) (fun _=>u) (qval i) 0:ℝ)
    (fun e=>(shift M L (qval i e) (b i) (tail i):ℝ))

lemma literalJoint_eq_orbit (M : ℕ) (hM : 0<M) (L : ℤ) (b : ∀ i,Label (m i))
    (tail : ∀ i,Fin (m i)→ℤ) (pstar slot : ι→ℤ) (qval : ∀ i,Fin (q i)→ℤ)
    (g x : ∀ i,G i) (u : ℤ) :
    literalJoint G n q m c hsk A w hA hw M L b tail pstar slot qval g x u=
      JointArrays.orbit G n q c hsk A w hA hw g x (fun i=>∏ j,tail i j)
        (fun i=>(exponent M L (b i) (tail i) (pstar i) (slot i)
          (fun _ : Fin 1=>1) (fun _=>0) (qval i) 0:ℝ))
        (fun i e=>(shift M L (qval i e) (b i) (tail i):ℝ)) u := by
  funext i
  apply Subtype.ext
  funext z
  rw [JointArrays.orbit_apply]
  change realPower (c i) (g i)
      ((exponent M L (b i) (tail i) (pstar i) (slot i) (fun _ : Fin 1=>1) (fun _=>u) (qval i) 0:ℝ)+
        ∑ e,(shift M L (qval i e) (b i) (tail i):ℝ)*z e)*x i=_
  rw [exponent_column_affine M hM]
  push_cast
  rfl

 

theorem literal_joint_factorization
    (hmono : ∀ i,Monotone (w i)) (Γ : ∀ i,Subgroup (G i))
    (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z)
    (s : ℕ) (h0 : ∀ i,(A i).level 0=⊤) (h1 : ∀ i,(A i).level 1=⊤)
    (hs : ∀ i,(A i).level (s+1)=⊥)
    (M : ℕ→ℕ) (hM : ∀ N,0<M N) (L : ℕ→ℤ)
    (b : ℕ → ∀ i,Label (m i)) (tail : ℕ → ∀ i,Fin (m i)→ℤ)
    (pstar slot : ℕ→ι→ℤ) (qval : ℕ → ∀ i,Fin (q i)→ℤ) (g x : ℕ→∀ i,G i)
    (Z : ℕ→ℝ) (hZ : ∀ N,0<Z N) :
    ∃ e : RealCoordinates (JointArrays.Carrier G n q c hsk A w hA)
      (Fintype.card (FiniteProducts.Index (JointArrays.dimension n q w))),
    ∃ B : CoveredLattice e (JointArrays.lattice G n q c hsk A w hA Γ),
      SecondKind e ∧
      (∀ k f,f∈(JointArrays.filtration G n q c hsk A w hA).level k ↔
        ∀ j,JointArrays.jointWeight n q w j<k → e.coord f j=0) ∧
      (∀ f,IsRational e f → ∀ i (u : Fin (q i)→ℤ),
        IsRational (c i) ((f i).val (fun j=>(u j:ℝ)))) ∧
      Nonempty (AllLevelFactorization.Factorization e B.small s
        (JointArrays.filtration G n q c hsk A w hA)
        (fun N=>literalJoint G n q m c hsk A w hA hw (M N) (L N) (b N) (tail N)
          (pstar N) (slot N) (qval N) (g N) (x N)) Z)
 := by
  have he : (fun N=>literalJoint G n q m c hsk A w hA hw (M N) (L N) (b N) (tail N)
      (pstar N) (slot N) (qval N) (g N) (x N))=
      (fun N=>JointArrays.orbit G n q c hsk A w hA hw (g N) (x N) (fun i=>∏ j,tail N i j)
        (fun i=>(exponent (M N) (L N) (b N i) (tail N i) (pstar N i) (slot N i)
          (fun _ : Fin 1=>1) (fun _=>0) (qval N i) 0:ℝ))
        (fun i e=>(shift (M N) (L N) (qval N i e) (b N i) (tail N i):ℝ))) := by
    funext N u
    exact literalJoint_eq_orbit G n q m c hsk A w hA hw (M N) (hM N) (L N) (b N) (tail N)
      (pstar N) (slot N) (qval N) (g N) (x N) u
  rw [he]
  exact JointArrays.factorization_exists G n q c hsk A w hA hw hmono Γ hΓ s h0 h1 hs
    g x _ _ _ Z hZ

end SourceIntegerArrays

end

end OAI
