import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice04
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
end
end
 

 
section
noncomputable section
namespace MalcevPrefixQuotient
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n r : ℕ}
variable (c : RealCoordinates G n) (hr : r ≤ n)
variable (N : Subgroup G) [N.Normal]
variable (hN : ∀ g : G, g ∈ N ↔ ∀ i : Fin n, i.val < r → c.coord g i = 0)

omit [N.Normal] in
lemma represent_coordinates (x : G ⧸ N) (i : Fin n) :
    c.coord (represent c (coordinates c hr N hN x)) i =
      if h : i.val < r then coordinates c hr N hN x ⟨i.val,h⟩ else 0 := by
  simp [represent,lift]

lemma quotient_coordinates_mk (g : G) (i : Fin r) :
    (quotientChart c hr N hN).coord (QuotientGroup.mk g) i = c.coord g (embed hr i) := rfl

 

theorem quotient_lattice (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z) (x : G ⧸ N) :
    x ∈ Γ.map (QuotientGroup.mk' N) ↔
      ∀ i, ∃ z : ℤ, (quotientChart c hr N hN).coord x i = z := by
  constructor
  · rintro ⟨g,hg,rfl⟩ i
    exact (hΓ g).mp hg (embed hr i)
  · intro hx
    refine ⟨represent c (coordinates c hr N hN x),?_,rebuild_coordinates c hr N hN x⟩
    apply (hΓ _).mpr
    intro i
    rw [represent_coordinates]
    split_ifs with hi
    · exact hx ⟨i.val,hi⟩
    · exact ⟨0,by simp⟩

 
theorem quotient_adapted (K : Subgroup G) (s : ℕ)
    (hK : ∀ g : G, g ∈ K ↔ ∀ i : Fin n, i.val < s → c.coord g i = 0) (x : G ⧸ N) :
    x ∈ K.map (QuotientGroup.mk' N) ↔
      ∀ i : Fin r, i.val < s → (quotientChart c hr N hN).coord x i = 0 := by
  constructor
  · rintro ⟨g,hg,rfl⟩ i hi
    exact (hK g).mp hg (embed hr i) hi
  · intro hx
    refine ⟨represent c (coordinates c hr N hN x),?_,rebuild_coordinates c hr N hN x⟩
    apply (hK _).mpr
    intro i hi
    rw [represent_coordinates]
    split_ifs with hir
    · exact hx ⟨i.val,hir⟩ hi
    · rfl

 

theorem quotient_rational (x : G ⧸ N) : IsRational (quotientChart c hr N hN) x ↔
    ∃ g : G, IsRational c g ∧ (QuotientGroup.mk g : G ⧸ N) = x := by
  constructor
  · intro hx
    refine ⟨represent c (coordinates c hr N hN x),?_,rebuild_coordinates c hr N hN x⟩
    intro i
    rw [represent_coordinates]
    split_ifs with hi
    · exact hx ⟨i.val,hi⟩
    · exact ⟨0,by simp⟩
  · rintro ⟨g,hg,rfl⟩ i
    exact hg (embed hr i)

end MalcevPrefixQuotient
end
end
 

 
section
noncomputable section
namespace PairTail
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : Subgroup G) [K.Normal]

 
def square : Subgroup (G × G) where
  carrier := {x | x.1⁻¹*x.2 ∈ K}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have hh := K.mul_mem ((inferInstance : K.Normal).conj_mem _ ha b.1⁻¹) hb
    simpa [mul_assoc] using hh
  inv_mem' := by
    intro a ha
    have hh := (inferInstance : K.Normal).conj_mem _ (K.inv_mem ha) a.1
    simpa [mul_assoc] using hh

def first : square K →* G := (MonoidHom.fst G G).comp (square K).subtype

def difference (x : square K) : K := ⟨x.val.1⁻¹*x.val.2,x.property⟩

def pair (g : G) (u : K) : square K := ⟨(g,g*u),by change g⁻¹*(g*u) ∈ K; simp⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma first_pair (g : G) (u : K) : first K (pair K g u) = g := rfl
omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma difference_pair (g : G) (u : K) : difference K (pair K g u) = u := by
  apply Subtype.ext
  simp [difference,pair]
omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma pair_first_difference (x : square K) : pair K (first K x) (difference K x) = x := by
  apply Subtype.ext
  ext <;> simp [pair,first,difference]
omit [IsTopologicalGroup G] in
lemma first_continuous : Continuous (first K) := continuous_fst.comp continuous_subtype_val
lemma difference_continuous : Continuous (difference K) := by
  apply Continuous.subtype_mk
  exact ((continuous_fst.comp continuous_subtype_val).inv).mul
    (continuous_snd.comp continuous_subtype_val)
lemma pair_continuous : Continuous (fun x : G × K => pair K x.1 x.2) := by
  apply Continuous.subtype_mk
  exact continuous_fst.prodMk (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))

def squareHomeomorph : square K ≃ₜ G × K where
  toFun x := (first K x,difference K x)
  invFun x := pair K x.1 x.2
  left_inv := pair_first_difference K
  right_inv x := by simp
  continuous_toFun := (first_continuous K).prodMk (difference_continuous K)
  continuous_invFun := pair_continuous K

variable (N : Subgroup G)
 
def diagonal : Subgroup (square K) where
  carrier := {x | x.val.1 ∈ N ∧ x.val.2 = x.val.1}
  one_mem' := ⟨N.one_mem,rfl⟩
  mul_mem' := by
    rintro a b ⟨ha,hea⟩ ⟨hb,heb⟩
    exact ⟨N.mul_mem ha hb,by change a.val.2*b.val.2 = a.val.1*b.val.1; rw [hea,heb]⟩
  inv_mem' := by
    rintro a ⟨ha,he⟩
    exact ⟨N.inv_mem ha,by change a.val.2⁻¹ = a.val.1⁻¹; rw [he]⟩

variable (hcent : N ≤ Subgroup.center G)
include hcent in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma diagonal_normal : (diagonal K N).Normal where
  conj_mem x hx y := by
    rcases hx with ⟨hx,he⟩
    have hc := Subgroup.mem_center_iff.mp (hcent hx)
    have h1 : y.val.1*x.val.1*y.val.1⁻¹ = x.val.1 := by
      rw [hc y.val.1]; simp [mul_assoc]
    have h2 : y.val.2*x.val.2*y.val.2⁻¹ = x.val.1 := by
      rw [he,hc y.val.2]; simp [mul_assoc]
    exact ⟨by change y.val.1*x.val.1*y.val.1⁻¹ ∈ N; rw [h1]; exact hx,
      by change y.val.2*x.val.2*y.val.2⁻¹ = y.val.1*x.val.1*y.val.1⁻¹; rw [h1,h2]⟩

include hcent in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma eq_coset_iff (x y : square K) :
    (QuotientGroup.mk x : square K ⧸ diagonal K N) = QuotientGroup.mk y ↔
    (QuotientGroup.mk (first K x) : G ⧸ N) = QuotientGroup.mk (first K y) ∧
      difference K x = difference K y := by
  rw [QuotientGroup.eq,QuotientGroup.eq]
  change (x.val.1⁻¹*y.val.1 ∈ N ∧ x.val.2⁻¹*y.val.2 = x.val.1⁻¹*y.val.1) ↔ _
  change _ ↔ x.val.1⁻¹*y.val.1 ∈ N ∧ difference K x = difference K y
  constructor
  · rintro ⟨hn,he⟩
    refine ⟨hn,Subtype.ext ?_⟩
    change x.val.1⁻¹*x.val.2 = y.val.1⁻¹*y.val.2
    have hc := Subgroup.mem_center_iff.mp (hcent hn)
    have hy : y.val.2 = x.val.2*(x.val.1⁻¹*y.val.1) := by rw [← he]; simp
    rw [hy]
    symm
    calc
      y.val.1⁻¹*(x.val.2*(x.val.1⁻¹*y.val.1)) =
          (y.val.1⁻¹*x.val.2)*(x.val.1⁻¹*y.val.1) := by group
      _ = (x.val.1⁻¹*y.val.1)*(y.val.1⁻¹*x.val.2) := hc _
      _ = _ := by group
  · rintro ⟨hn,hd⟩
    refine ⟨hn,?_⟩
    have hd' := congrArg Subtype.val hd
    change x.val.1⁻¹*x.val.2 = y.val.1⁻¹*y.val.2 at hd'
    have hy : y.val.2 = y.val.1*(x.val.1⁻¹*x.val.2) := by rw [hd']; simp
    have hc := Subgroup.mem_center_iff.mp (hcent hn)
    rw [hy]
    calc
      x.val.2⁻¹*(y.val.1*(x.val.1⁻¹*x.val.2)) =
          x.val.2⁻¹*x.val.1*(x.val.1⁻¹*y.val.1)*(x.val.1⁻¹*x.val.2) := by group
      _ = (x.val.1⁻¹*y.val.1)*(x.val.2⁻¹*x.val.1)*(x.val.1⁻¹*x.val.2) := by
        rw [hc (x.val.2⁻¹*x.val.1)]
      _ = x.val.1⁻¹*y.val.1 := by group

def quotientCoordinates (x : square K ⧸ diagonal K N) : (G ⧸ N) × K :=
  Quotient.lift (fun x : square K => (QuotientGroup.mk (first K x),difference K x))
    (by
      intro x y he
      have h := (eq_coset_iff K N hcent x y).mp (Quotient.sound he)
      exact Prod.ext h.1 h.2) x

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma quotientCoordinates_mk (x : square K) :
    quotientCoordinates K N hcent (QuotientGroup.mk x) =
      (QuotientGroup.mk (first K x),difference K x) := rfl
lemma quotientCoordinates_continuous : Continuous (quotientCoordinates K N hcent) := by
  rw [(QuotientGroup.isQuotientMap_mk (diagonal K N)).continuous_iff]
  exact (QuotientGroup.continuous_mk.comp (first_continuous K)).prodMk (difference_continuous K)

variable (s : G ⧸ N → G) (hs : ∀ x, (QuotientGroup.mk (s x) : G ⧸ N) = x)
variable (hsc : Continuous s)
def quotientRebuild (x : (G ⧸ N) × K) : square K ⧸ diagonal K N :=
  QuotientGroup.mk (pair K (s x.1) x.2)
include hs in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma quotientCoordinates_rebuild (x : (G ⧸ N) × K) :
    quotientCoordinates K N hcent (quotientRebuild K N s x) = x := by
  simp [quotientRebuild,hs]
include hs in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma quotientRebuild_coordinates (x : square K ⧸ diagonal K N) :
    quotientRebuild K N s (quotientCoordinates K N hcent x) = x := by
  induction x using Quotient.inductionOn with | h x =>
    apply (eq_coset_iff K N hcent _ _).mpr
    simp [quotientCoordinates_mk,hs]
include hsc in
lemma quotientRebuild_continuous : Continuous (quotientRebuild K N s) := by
  exact QuotientGroup.continuous_mk.comp ((pair_continuous K).comp
    ((hsc.comp continuous_fst).prodMk continuous_snd))

def quotientHomeomorph : (square K ⧸ diagonal K N) ≃ₜ (G ⧸ N) × K where
  toFun := quotientCoordinates K N hcent
  invFun := quotientRebuild K N s
  left_inv := quotientRebuild_coordinates K N hcent s hs
  right_inv := quotientCoordinates_rebuild K N hcent s hs
  continuous_toFun := quotientCoordinates_continuous K N hcent
  continuous_invFun := quotientRebuild_continuous K N s hsc

end PairTail
end
end
 

 
section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace RationalPolynomialMap
variable {σ τ : Type*}

def IsPolynomial (f : (σ → ℝ) → ℝ) : Prop :=
  ∃ P : MvPolynomial σ ℚ, ∀ x, f x = MvPolynomial.eval₂ (algebraMap ℚ ℝ) x P

lemma const (q : ℚ) : IsPolynomial (fun _ : σ → ℝ => (q:ℝ)) := ⟨MvPolynomial.C q,by simp⟩
lemma zero : IsPolynomial (fun _ : σ → ℝ => (0:ℝ)) := by simpa using const (σ:=σ) 0
lemma one : IsPolynomial (fun _ : σ → ℝ => (1:ℝ)) := by simpa using const (σ:=σ) 1
lemma coordinate (i : σ) : IsPolynomial (fun x : σ → ℝ => x i) := ⟨MvPolynomial.X i,by simp⟩
lemma add {f g : (σ → ℝ) → ℝ} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun x => f x+g x) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,by simp [hp,hq]⟩
lemma mul {f g : (σ → ℝ) → ℝ} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun x => f x*g x) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,by simp [hp,hq]⟩
lemma neg {f : (σ → ℝ) → ℝ} (hf : IsPolynomial f) : IsPolynomial (fun x => -f x) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨-p,by simp [hp]⟩
lemma sub {f g : (σ → ℝ) → ℝ} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun x => f x-g x) := by simpa [sub_eq_add_neg] using add hf (neg hg)

lemma eval {f : τ → (σ → ℝ) → ℝ} (hf : ∀ i, IsPolynomial (f i))
    (P : MvPolynomial τ ℚ) : IsPolynomial (fun x =>
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => f i x) P) := by
  induction P using MvPolynomial.induction_on with
  | C q => simpa using const (σ:=σ) q
  | add p q hp hq => simpa using add hp hq
  | mul_X p i hp => simpa using mul hp (hf i)

lemma comp {f : (τ → ℝ) → ℝ} (hf : IsPolynomial f) {g : (σ → ℝ) → (τ → ℝ)}
    (hg : ∀ i, IsPolynomial (fun x => g x i)) : IsPolynomial (fun x => f (g x)) := by
  obtain ⟨p,hp⟩ := hf
  simpa only [hp] using eval hg p

lemma polynomial_eval (P : ℚ[X]) {f : (σ → ℝ) → ℝ} (hf : IsPolynomial f) :
    IsPolynomial (fun x => P.eval₂ (algebraMap ℚ ℝ) (f x)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa using add hp hq
  | monomial i a =>
    have hi : IsPolynomial (fun x => (f x)^i) := by
      induction i with
      | zero => simpa using one (σ:=σ)
      | succ i ih => simpa only [pow_succ] using mul ih hf
    simpa using mul (const a) hi
end RationalPolynomialMap

end
end
end
end
end

end OAI
