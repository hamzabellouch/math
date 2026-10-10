import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughLiteral01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end

end
 

section
 
noncomputable section
namespace RoughProductRemoval
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional
open scoped BigOperators

 

def nestedBox {v : ℕ} (lo hi : Fin v → ℝ) (res A : Fin v → ℤ)
    (d M : ℕ) (q : ℤ) : Finset (Fin v → ℤ) := by
  classical
  exact (physicalResidueBox lo hi res d).filter (fun x => ∀ i, q ∣ (M:ℤ)*x i+A i)

variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]

def badProduct (m v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z : ℝ)
    (d M : ℕ) (A : Fin v → ℤ) (P : (Fin (m+v) → ℝ) → G) (t : Fin m → ℤ) : Prop :=
  ∃ (lo hi : Fin v → ℝ) (res : Fin v → ℤ) (test : (G⧸Γ) → ℂ),
    (∀ i,c₀*Z≤hi i-lo i) ∧ (∀ i,-C₀*Z≤lo i ∧ hi i≤C₀*Z) ∧
    LipschitzWith B test ∧ (∀ y,‖test y‖≤B) ∧
    η≤‖mean (physicalResidueBox lo hi res d)
      (fun x=>test (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ))))))-
    mean (nestedBox lo hi res A d M (∏ j,t j))
      (fun x=>test (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ))))))‖

def productTimes {m : ℕ} (S : Fin m → ℝ) (r : Fin m → ℤ) (L : ℤ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset (fun j => times (S j) (r j) L)

def exceptionalProduct (m v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z : ℝ)
    (d M : ℕ) (A : Fin v → ℤ) (P : (Fin (m+v) → ℝ) → G)
    (S : Fin m → ℝ) (r : Fin m → ℤ) (L : ℤ) : Finset (Fin m → ℤ) := by
  classical
  exact (productTimes S r L).filter (badProduct Γ m v c₀ C₀ B η Z d M A P)

end RoughProductRemoval
end
end
 

section
 
 

noncomputable section
namespace RoughProductRemoval
open RoughSamplingWeights FinitePieceAverages
open scoped BigOperators

lemma linear_divisibility_class (M q : ℕ) (hc : M.Coprime q) (A : ℤ) :
    ∃ b : ℤ,∀ x : ℤ,(q:ℤ)∣(M:ℤ)*x+A ↔ x ≡ b [ZMOD q] := by
  obtain ⟨b,hb⟩ := residue_parameter M q hc A 0
  refine ⟨b,fun x=>?_⟩
  have he : (q:ℤ)∣(M:ℤ)*x+A ↔ A+(M:ℤ)*x ≡ 0 [ZMOD q] := by
    rw [Int.modEq_zero_iff_dvd]
    simp only [add_comm]
  exact he.trans (hb x)

lemma parent_residue (d M q : ℕ) (hd : 0<d) (hq : 0<q)
    (hdq : d.Coprime q) (hMq : M.Coprime q) (a A : ℤ) :
    ∃ u : ℤ, 0≤u ∧ u<(d*q:ℕ) ∧
      ∀ x : ℤ,(x ≡ a [ZMOD d] ∧ (q:ℤ)∣(M:ℤ)*x+A) ↔ x ≡ u [ZMOD d*q] := by
  obtain ⟨b,hb⟩ := linear_divisibility_class M q hMq A
  obtain ⟨j,hj⟩ := residue_parameter d q hdq a b
  let u₀ : ℤ := a+(d:ℤ)*j
  have hu₀q : u₀ ≡ b [ZMOD q] := (hj j).mpr (.refl _)
  have hu₀d : u₀ ≡ a [ZMOD d] := by simp [u₀]
  have hdqpos : (0:ℤ)<(d:ℤ)*q := by positivity
  obtain ⟨u,hu0,hult,hue⟩ := Int.existsUnique_equiv u₀ hdqpos
  refine ⟨u,hu0,by exact_mod_cast hult,fun x=>?_⟩
  rw [hb]
  have he : (x ≡ a [ZMOD d] ∧ x ≡ b [ZMOD q]) ↔
      (x ≡ u₀ [ZMOD d] ∧ x ≡ u₀ [ZMOD q]) := by
    constructor
    · rintro ⟨ha,hb⟩
      exact ⟨ha.trans hu₀d.symm,hb.trans hu₀q.symm⟩
    · rintro ⟨ha,hb⟩
      exact ⟨ha.trans hu₀d,hb.trans hu₀q⟩
  rw [he,Int.modEq_and_modEq_iff_modEq_mul (by simpa using hdq)]
  exact ⟨fun h=>h.trans hue.symm,fun h=>h.trans hue⟩

lemma parent_vector {v : ℕ} (d M q : ℕ) (hd : 0<d) (hq : 0<q)
    (hdq : d.Coprime q) (hMq : M.Coprime q) (a A : Fin v → ℤ) :
    ∃ u : Fin v → ℤ,(∀ i,0≤u i ∧ u i<(d*q:ℕ)) ∧
      ∀ x : Fin v → ℤ,
        ((∀ i,x i ≡ a i [ZMOD d]) ∧ (∀ i,(q:ℤ)∣(M:ℤ)*x i+A i)) ↔
          ∀ i,x i ≡ u i [ZMOD d*q] := by
  choose u hu0 hult hu using fun i=>parent_residue d M q hd hq hdq hMq (a i) (A i)
  refine ⟨u,fun i=>⟨hu0 i,hult i⟩,fun x=>?_⟩
  rw [← forall_and]
  exact forall_congr' (fun i=>hu i (x i))

lemma nestedBox_eq_parent {v : ℕ} (d M q : ℕ) (hd : 0<d) (hq : 0<q)
    (hdq : d.Coprime q) (hMq : M.Coprime q) (a A : Fin v → ℤ) :
    ∃ u : Fin v → ℤ,(∀ i,0≤u i ∧ u i<(d*q:ℕ)) ∧
      (∀ i,(q:ℤ)∣(M:ℤ)*u i+A i) ∧
      ∀ lo hi,nestedBox lo hi a A d M q = physicalResidueBox lo hi u (d*q) := by
  classical
  obtain ⟨u,hu,he⟩ := parent_vector d M q hd hq hdq hMq a A
  refine ⟨u,hu,((he u).mpr (fun i=>.refl _)).2,?_⟩
  intro lo hi
  ext x
  simp only [nestedBox,physicalResidueBox,Finset.mem_filter]
  rw [and_assoc,he x]
  norm_cast

 

lemma nested_linear_parameter (d M q t : ℕ) (hq : 0<q)
    (hc : (M*d).Coprime t) (u A : ℤ) (hu : (q:ℤ)∣(M:ℤ)*u+A) :
    ∃ b : ℤ,∀ y : ℤ,
      ((q*t:ℕ):ℤ)∣(M:ℤ)*(u+((d*q:ℕ):ℤ)*y)+A ↔ y ≡ b [ZMOD t] := by
  obtain ⟨a,ha⟩ := hu
  obtain ⟨b,hb⟩ := linear_divisibility_class (M*d) t hc a
  refine ⟨b,fun y=>?_⟩
  have hq0 : (q:ℤ)≠0 := by positivity
  have he : (M:ℤ)*(u+((d*q:ℕ):ℤ)*y)+A=(q:ℤ)*(((M*d:ℕ):ℤ)*y+a) := by
    push_cast
    nlinarith [ha]
  rw [he,Nat.cast_mul,mul_dvd_mul_iff_left hq0,hb]

lemma nested_removed_class {v : ℕ} (d M q t : ℕ) (hq : 0<q)
    (hc : (M*d).Coprime t) (u A : Fin v → ℤ)
    (hu : ∀ i,(q:ℤ)∣(M:ℤ)*u i+A i) :
    ∃ b : Fin v → ℤ,∀ y : Fin v → ℤ,
      (∀ i,((q*t:ℕ):ℤ)∣(M:ℤ)*integerAffine u (d*q) y i+A i) ↔
        ∀ i,y i ≡ b i [ZMOD t] := by
  choose b hb using fun i=>nested_linear_parameter d M q t hq hc (u i) (A i) (hu i)
  exact ⟨b,fun y=>forall_congr' (fun i=>hb i (y i))⟩

lemma nestedBox_refine {v : ℕ} (lo hi : Fin v → ℝ) (a A : Fin v → ℤ)
    (d M q t : ℕ) :
    nestedBox lo hi a A d M (q*t) =
      (nestedBox lo hi a A d M q).filter (fun x=>∀ i,((q*t:ℕ):ℤ)∣(M:ℤ)*x i+A i) := by
  classical
  ext x
  simp only [nestedBox,Finset.mem_filter]
  constructor
  · rintro ⟨hmem,hdiv⟩
    refine ⟨⟨hmem,fun i=>?_⟩,hdiv⟩
    exact (by exact ⟨(t:ℤ),by push_cast; rfl⟩ : (q:ℤ)∣((q*t:ℕ):ℤ)).trans (hdiv i)
  · exact fun h=>⟨h.1.1,h.2⟩

 

theorem nested_residue_means {v : ℕ} (d M q : ℕ) (hd : 0<d) (hq : 0<q)
    (hdq : d.Coprime q) (hMq : M.Coprime q)
    (a A : Fin v → ℤ) :
    ∃ u : Fin v → ℤ,(∀ i,0≤u i ∧ u i<(d*q:ℕ)) ∧
      ∀ t : ℕ,(M*d).Coprime t →∃ b : Fin v → ℤ,
      ∀ (lo hi : Fin v → ℝ) (f : (Fin v → ℤ) → ℂ),
      mean (nestedBox lo hi a A d M q) f =
        mean (boxIndices (rescaledEndpoint lo u (d*q)) (rescaledEndpoint hi u (d*q))
          (fun _=>0) 1) (fun y=>f (integerAffine u (d*q) y)) ∧
      mean (nestedBox lo hi a A d M (q*t)) f =
        mean (physicalResidueBox (rescaledEndpoint lo u (d*q))
          (rescaledEndpoint hi u (d*q)) b t) (fun y=>f (integerAffine u (d*q) y)) := by
  classical
  obtain ⟨u,hu,hud,he⟩ := nestedBox_eq_parent d M q hd hq hdq hMq a A
  refine ⟨u,hu,?_⟩
  intro t hc
  obtain ⟨b,hb⟩ := nested_removed_class d M q t hq hc u A hud
  have hK : 0<d*q := Nat.mul_pos hd hq
  refine ⟨b,fun lo hi f=>⟨?_,?_⟩⟩
  · rw [he]
    exact residue_mean lo hi u (d*q) hK f
  · rw [nestedBox_refine,he,physical_residue_reparametrization lo hi u (d*q) hK,
      Finset.filter_image]
    have hp : (fun y : Fin v → ℤ=>∀ i,((q*t:ℕ):ℤ)∣(M:ℤ)*integerAffine u (d*q) y i+A i)=
        (fun y : Fin v → ℤ=>∀ i,y i ≡ b i [ZMOD t]) :=
      funext (fun y=>propext (hb y))
    simp only [hp]
    convert mean_image (physicalResidueBox (rescaledEndpoint lo u (d*q))
      (rescaledEndpoint hi u (d*q)) b t) (integerAffine u (d*q))
      (affine_injective u (d*q) hK) f using 1
    congr 2
    ext y
    simp only [physicalResidueBox,Finset.mem_filter]

end RoughProductRemoval
end
end
 

section
 
 

noncomputable section
namespace RoughProductRemoval
open RationalLattice MalcevCharacters RealPolynomialDegree RoughPolynomialDegree
open RoughSamplingWeights

 

def firstLift {m v : ℕ} (t : Fin m → ℝ) (u : Fin v → ℤ) (K : ℕ)
    (y : Fin (v+1) → ℝ) : Fin ((m+1)+v) → ℝ :=
  Fin.append (Fin.cons (y 0) t) (fun i=>(u i:ℝ)+(K:ℝ)*y i.succ)

lemma firstLift_degree {m v : ℕ} (t : Fin m → ℝ) (u : Fin v → ℤ) (K : ℕ)
    (i : Fin ((m+1)+v)) : HasDegree (fun y=>firstLift t u K y i) 1 := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.cases ?_ (fun k=>?_) j
    · simpa only [firstLift,Fin.append_left,Fin.cons_zero] using
        (coordinate (0:Fin (v+1)))
    · simpa only [firstLift,Fin.append_left,Fin.cons_succ] using
        (RealPolynomialDegree.const (σ:=Fin (v+1)) (t k) 1)
  · intro j
    simpa only [firstLift,Fin.append_right,max_self] using
      (RealPolynomialDegree.add (RealPolynomialDegree.const (σ:=Fin (v+1)) (u j:ℝ) 1)
        (RealPolynomialDegree.scale (coordinate j.succ) (K:ℝ)))

lemma firstLift_eval {m v : ℕ} (t : Fin m → ℤ) (u : Fin v → ℤ) (K : ℕ)
    (s : ℤ) (x : Fin v → ℤ) :
    firstLift (fun j=>(t j:ℝ)) u K (Fin.cons (s:ℝ) (fun i=>(x i:ℝ))) =
      Fin.append (fun j=>(((Fin.cons s t : Fin (m+1) → ℤ) j):ℝ))
        (fun i=>(integerAffine u K x i:ℝ)) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.cases ?_ (fun k=>?_) j <;>
      simp only [firstLift,Fin.append_left,Fin.cons_zero,Fin.cons_succ]
  · intro j
    simp only [firstLift,Fin.append_right,Fin.cons_succ,integerAffine,Int.cast_add,
      Int.cast_mul,Int.cast_natCast]

 
def tailLift {m v : ℕ} (a : ℝ) (y : Fin (m+v) → ℝ) : Fin ((m+1)+v) → ℝ :=
  Fin.append (Fin.cons a (fun j=>y (j.castAdd v))) (fun i=>y (i.natAdd m))

lemma tailLift_degree {m v : ℕ} (a : ℝ) (i : Fin ((m+1)+v)) :
    HasDegree (fun y=>tailLift a y i) 1 := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.cases ?_ (fun k=>?_) j
    · simpa only [tailLift,Fin.append_left,Fin.cons_zero] using
        (RealPolynomialDegree.const (σ:=Fin (m+v)) a 1)
    · simpa only [tailLift,Fin.append_left,Fin.cons_succ] using coordinate (k.castAdd v)
  · intro j
    simpa only [tailLift,Fin.append_right] using coordinate (j.natAdd m)

lemma tailLift_eval {m v : ℕ} (a : ℝ) (t : Fin m → ℝ) (x : Fin v → ℝ) :
    tailLift a (Fin.append t x)=Fin.append (Fin.cons a t) x := by
  simp only [tailLift,Fin.append_left,Fin.append_right]

variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (c : RealCoordinates G dim)

lemma first_polynomial {m v D : ℕ} (P : (Fin ((m+1)+v) → ℝ) → G)
    (hP : ∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D)
    (t : Fin m → ℝ) (u : Fin v → ℤ) (K : ℕ) :
    ∀ i,HasDegree (fun y=>canonicalLog c (P (firstLift t u K y)) i) D := by
  intro i
  simpa only [one_mul] using compose (hP i) (fun j y=>firstLift t u K y j)
    (firstLift_degree t u K)

lemma tail_polynomial {m v D : ℕ} (P : (Fin ((m+1)+v) → ℝ) → G)
    (hP : ∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) (a : ℝ) :
    ∀ i,HasDegree (fun y=>canonicalLog c (P (tailLift a y)) i) D := by
  intro i
  simpa only [one_mul] using compose (hP i) (fun j y=>tailLift a y j)
    (tailLift_degree a)

end RoughProductRemoval

end
end

end OAI
