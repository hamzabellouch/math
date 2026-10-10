import OAI.Analysis.Naimark.Homogeneity

namespace OAI

noncomputable section

namespace NaimarkZFC

namespace PeakingPairData

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def AmbientPresentation (G : PeakingPairData A)
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] (_hp : ∀ i n, G.peak i n ∈ S)
    (z : A) (T : StarSubalgebra ℂ A) [IsClosed (T : Set A)] : Prop :=
  G.HNNAmbientPresentation S.subtype T.subtype (starPair z)

lemma AmbientPresentation.generated (G : PeakingPairData A)
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] (hp : ∀ i n, G.peak i n ∈ S)
    (z : A) (T : StarSubalgebra ℂ A) [IsClosed (T : Set A)]
    (h : G.AmbientPresentation S hp z T) :
    T = hnnGenerated S.subtype (starPair z) := by
  have H := HNNAmbientPresentation.generated G S.subtype T.subtype (starPair z)
    Subtype.val_injective h
  have hr : T.subtype.range = T := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩; exact b.property
    · intro ha; exact ⟨⟨a,ha⟩,rfl⟩
  exact hr.symm.trans H

end

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem ambient_presentation_swap (P Q : PeakingPairData A)
    (S R T U : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (R : Set A)]
    [IsClosed (T : Set A)] [IsClosed (U : Set A)]
    (hTU : T ≤ U)
    (pS : ∀ i n, P.peak i n ∈ S) (qS : ∀ i n, Q.peak i n ∈ S)
    (pT : ∀ i n, P.peak i n ∈ T) (qR : ∀ i n, Q.peak i n ∈ R)
    (z w : A) (ht : ∀ a, P.trace a = Q.trace a)
    (hP : P.AmbientPresentation S pS z R)
    (hQ : Q.AmbientPresentation S qS w T)
    (hR : Q.AmbientPresentation R qR w U) :
    P.AmbientPresentation T pT z U :=
  HNNAmbientPresentation.swap P Q S.subtype R.subtype T.subtype U.subtype
    Subtype.val_injective Subtype.val_injective Subtype.val_injective
    (StarSubalgebra.inclusion hTU) (fun _ => rfl) (starPair z) (starPair w)
    ht hP hQ hR (P.onSubalgebra T pT) (fun _ _ => rfl) (fun _ => rfl)

end

section
attribute [local instance] hnnGenerated_isClosed ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A S X Y : Type}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [CStarAlgebra Y] [partialOrderY : PartialOrder Y] [starOrderedRingY : StarOrderedRing Y]

omit partialOrderY starOrderedRingY in
lemma HNNAmbientPresentation.inherited [PartialOrder Y] [StarOrderedRing Y] (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (x : X →⋆ₐ[ℂ] A) (y : Y →⋆ₐ[ℂ] A)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (f : S →⋆ₐ[ℂ] X) (hf : ∀ a, x (f a) = b a) (z : Bool → A)
    (h : G.HNNAmbientPresentation x y z)
    (B : PeakingPairData S) (hp : ∀ i n, b (B.peak i n) = G.peak i n)
    (ht : ∀ a, B.trace a = G.trace (b a)) :
    G.HNNAmbientPresentation b (hnnGenerated b z).subtype z := by
  obtain ⟨D,hpD,htD,e,heb,hew,het⟩ := h
  let Ψ : D.HNNAlgebra →⋆ₐ[ℂ] A := y.comp e.toStarAlgHom
  have hΨ : Function.Injective Ψ := hy.comp e.injective
  have hpeak (i : Bool) (n : ℕ) : f (B.peak i n) = D.peak i n := by
    apply hx
    rw [hf,hp,hpD]
  have htrace (a : S) : D.trace (f a) = B.trace a := by
    rw [htD,hf,ht]
  have hb (a : S) : Ψ (D.hnnBase (f a)) = b a := (heb (f a)).trans (hf a)
  obtain ⟨e',he'b,he'w,he't⟩ := B.hnn_ambient_presentation D f hpeak htrace
    Ψ hΨ b z hb hew
  exact ⟨B,hp,ht,e',he'b,he'w,he't (positiveCLM G.trace) het⟩

end

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] hnnGenerated_isClosed
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem ambient_presentation_inherited (G : PeakingPairData A)
    (X Y S : StarSubalgebra ℂ A)
    [IsClosed (X : Set A)] [IsClosed (Y : Set A)] [IsClosed (S : Set A)]
    (pX : ∀ i n, G.peak i n ∈ X) (pS : ∀ i n, G.peak i n ∈ S)
    (z : A) (hSX : S ≤ X) (h : G.AmbientPresentation X pX z Y) :
    G.AmbientPresentation S pS z (hnnGenerated S.subtype (starPair z)) :=
  HNNAmbientPresentation.inherited G S.subtype X.subtype Y.subtype
    Subtype.val_injective Subtype.val_injective (StarSubalgebra.inclusion hSX)
    (fun _ => rfl) (starPair z) h (G.onSubalgebra S pS)
    (fun _ _ => rfl) (fun _ => rfl)

end

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma AmbientPresentation.congr (G : PeakingPairData A)
    (S S' T T' : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (S' : Set A)]
    [IsClosed (T : Set A)] [IsClosed (T' : Set A)]
    (pS : ∀ i n, G.peak i n ∈ S) (pS' : ∀ i n, G.peak i n ∈ S')
    (z : A) (hS : S = S') (hT : T = T')
    (h : G.AmbientPresentation S pS z T) : G.AmbientPresentation S' pS' z T' := by
  subst S'
  subst T'
  exact h

end

end PeakingPairData

namespace HNNWord
variable {A D I : Type*}

theorem AllCoefficients.mono {S T : Set A} (hst : S ⊆ T)
    (w : HNNWord A) (hw : w.AllCoefficients S) : w.AllCoefficients T := by
  induction w with
  | single i a => exact hst hw
  | cons i a w ih => exact ⟨hst hw.1,ih hw.2⟩

theorem allCoefficients_one_stage (S : I → Set A)
    (hdir : Directed (· ⊆ ·) S) (w : HNNWord A)
    (hw : w.AllCoefficients (⋃ i, S i)) (a : A) (ha : a ∈ ⋃ i, S i) :
    ∃ i, w.AllCoefficients (S i) ∧ a ∈ S i := by
  induction w generalizing a with
  | single s b =>
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hw
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ha
    obtain ⟨k,hik,hjk⟩ := hdir i j
    exact ⟨k,hik hi,hjk hj⟩
  | cons s b w ih =>
    obtain ⟨i,hi,hbi⟩ := ih hw.2 b hw.1
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ha
    obtain ⟨k,hik,hjk⟩ := hdir i j
    exact ⟨k,⟨hik hbi,hi.mono hik w⟩,hjk hj⟩

theorem lift_reduced (φ : D → A) (K : Bool → D → Prop) (L : Bool → A → Prop)
    (hreflect : ∀ i a, L i (φ a) → K i a) (w : HNNWord A)
    (hw : w.AllCoefficients (Set.range φ)) (hr : w.Reduced L) :
    ∃ u : HNNWord D, u.mapCoefficients φ = w ∧ u.Reduced K := by
  induction w with
  | single i a =>
    obtain ⟨b,rfl⟩ := hw
    exact ⟨.single i b,rfl,trivial⟩
  | cons i a w ih =>
    obtain ⟨b,rfl⟩ := hw.1
    obtain ⟨u,hu,hku⟩ := ih hw.2 hr.2
    refine ⟨.cons i b u,?_,?_,hku⟩
    · simp only [mapCoefficients,hu]
    · rcases hr.1 with hi | hi
      · left
        rw [← hu] at hi
        simpa only [first_mapCoefficients] using hi
      · exact Or.inr (hreflect i b hi)

end HNNWord

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [partialOrderC : PartialOrder C] [starOrderedRingC : StarOrderedRing C]

lemma turnCenter_natural (B : PeakingPairData A) (D : PeakingPairData C)
    (φ : A →⋆ₐ[ℂ] C) (hp : ∀ i n, φ (B.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (φ a) = B.trace a) (i : Bool) (a : A) :
    φ (B.turnCenter i a) = D.turnCenter i (φ a) := by
  simp only [turnCenter,map_sub,B.diagonal_natural D φ hp,
    B.expectation_natural D φ hp ht]

lemma turnRemainder_natural (B : PeakingPairData A) (D : PeakingPairData C)
    (φ : A →⋆ₐ[ℂ] C) (hp : ∀ i n, φ (B.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (φ a) = B.trace a) (i : Bool) (a : A) :
    φ (B.turnRemainder i a) = D.turnRemainder i (φ a) := by
  simp only [turnRemainder,B.diagonal_natural D φ hp,
    B.expectation_natural D φ hp ht]

lemma turnCentered_natural_iff (B : PeakingPairData A) (D : PeakingPairData C)
    (φ : A →⋆ₐ[ℂ] C) (hp : ∀ i n, φ (B.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (φ a) = B.trace a) (i : Bool) (a : A) :
    D.turnCentered i (φ a) ↔ B.turnCentered i a := by
  change (D.input false).expectation (!i) (φ a) = 0 ↔ _
  rw [B.expectation_natural D φ hp ht]
  rfl

def turnRemainderCLM (B : PeakingPairData A) (i : Bool) : A →L[ℂ] A :=
  (starAlgHomCLM (B.diagonal i)).comp ((B.input false).expectation (!i))

@[simp] lemma turnRemainderCLM_apply (B : PeakingPairData A) (i : Bool) (a : A) :
    B.turnRemainderCLM i a = B.turnRemainder i a := rfl

variable {I : Type*} (B : PeakingPairData A)
  (D : I → Type) [∀ i, CStarAlgebra (D i)]
  [∀ i, PartialOrder (D i)] [∀ i, StarOrderedRing (D i)]
  (P : ∀ i, PeakingPairData (D i)) (ι : ∀ i, D i →⋆ₐ[ℂ] A)
  (hp : ∀ i s n, ι i ((P i).peak s n) = B.peak s n)
  (ht : ∀ i a, B.trace (ι i a) = (P i).trace a)
  (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C)
  (F : ∀ i, (P i).HNNAlgebra →⋆ₐ[ℂ] C)
  (hFb : ∀ i a, F i ((P i).hnnBase a) = ψ (ι i a))
  (hFw : ∀ i s, F i ((P i).hnnLetter s) = w s)

include hp ht hFb hFw in
omit partialOrderC starOrderedRingC in
lemma inherited_turn [PartialOrder C] [StarOrderedRing C] (i : I) (s : Bool) (a : D i) :
    w s*ψ (ι i a)*w (!s) =
      w s*ψ (B.turnCenter s (ι i a))*w (!s) + ψ (B.turnRemainder s (ι i a)) := by
  have H := congrArg (F i) ((P i).hnnLetter_turn s a)
  simpa only [map_mul,map_add,hFb,hFw,
    (P i).turnCenter_natural B (ι i) (hp i) (ht i),
    (P i).turnRemainder_natural B (ι i) (hp i) (ht i)] using H

include hp ht in
lemma union_turnCenter_stable (s : Bool) (a : A)
    (ha : a ∈ ⋃ i, Set.range (ι i)) : B.turnCenter s a ∈ ⋃ i, Set.range (ι i) := by
  obtain ⟨i,b,rfl⟩ := Set.mem_iUnion.mp ha
  exact Set.mem_iUnion.mpr ⟨i,(P i).turnCenter s b,
    (P i).turnCenter_natural B (ι i) (hp i) (ht i) s b⟩

include hp ht hFb hFw in
omit partialOrderC starOrderedRingC in
lemma limit_reduced_moment [PartialOrder C] [StarOrderedRing C]
    (hdir : Directed (· ⊆ ·) (fun i => Set.range (ι i)))
    (g : C →L[ℂ] ℂ) (hFg : ∀ i b, g (F i b) = (P i).hnnTrace b)
    (u : HNNWord A) (a : A) (hu : u.Reduced B.turnCentered)
    (huc : u.AllCoefficients (⋃ i, Set.range (ι i)))
    (ha : a ∈ ⋃ i, Set.range (ι i)) : g (ψ a*u.eval ψ w) = 0 := by
  obtain ⟨i,hui,⟨b,rfl⟩⟩ := u.allCoefficients_one_stage
    (fun i => Set.range (ι i)) hdir huc a ha
  obtain ⟨v,rfl,hv⟩ := u.lift_reduced (ι i) (P i).turnCentered B.turnCentered
    (fun s c => ((P i).turnCentered_natural_iff B (ι i) (hp i) (ht i) s c).mp) hui hu
  have hvEval := v.eval_hom (P i).hnnBase (ψ.comp (ι i))
    (P i).hnnLetter w (F i) (hFb i) (hFw i)
  rw [HNNWord.eval_mapCoefficients]
  change g (ψ (ι i b)*v.eval (ψ.comp (ι i)) w) = 0
  rw [← hFb i b,← hvEval,← map_mul,hFg]
  rw [← (P i).hnnTrace_expectation,(P i).hnnExpectation_word v b hv,map_zero]

include hp ht hFb hFw in

theorem hnn_directed_limit_presentation [Nonempty I]
    (hdir : Directed (· ⊆ ·) (fun i => Set.range (ι i)))
    (hdense : Dense (⋃ i, Set.range (ι i)))
    (g : C →L[ℂ] ℂ) (hgs : IsState g)
    (hg : ∀ c : C, g (star c*c) = 0 → c = 0)
    (hFg : ∀ i b, g (F i b) = (P i).hnnTrace b)
    (hgen : Dense (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C)) :
    ∃ e : B.HNNAlgebra ≃⋆ₐ[ℂ] C,
      (∀ a, e (B.hnnBase a) = ψ a) ∧ (∀ s, e (B.hnnLetter s) = w s) ∧
      (∀ b, g (e b) = B.hnnTrace b) := by
  have hstar (s : Bool) : star (w s) = w (!s) := by
    obtain ⟨i⟩ := ‹Nonempty I›
    rw [← hFw i s,← map_star,(P i).hnnLetter_star,hFw]
  have hturn (s : Bool) (a : A) : w s*ψ a*w (!s) =
      w s*ψ (B.turnCenter s a)*w (!s) + ψ (B.turnRemainder s a) := by
    apply congrFun (Continuous.ext_on hdense
      (((continuous_const.mul (map_continuous ψ)).mul continuous_const))
      (((continuous_const.mul ((map_continuous ψ).comp (B.turnCenterCLM s).continuous)).mul
        continuous_const).add ((map_continuous ψ).comp (B.turnRemainderCLM s).continuous)) ?_) a
    rintro x hx
    obtain ⟨i,b,rfl⟩ := Set.mem_iUnion.mp hx
    exact B.inherited_turn D P ι hp ht ψ w F hFb hFw i s b
  have hbase (a : A) : g (ψ a) = B.trace a := by
    apply congrFun (Continuous.ext_on hdense (g.continuous.comp (map_continuous ψ)) (map_continuous B.trace) ?_) a
    rintro x hx
    obtain ⟨i,b,rfl⟩ := Set.mem_iUnion.mp hx
    change g (ψ (ι i b)) = B.trace (ι i b)
    rw [← hFb i b,hFg,(P i).hnnTrace_base,ht]
  exact B.hnn_limit_comparison ψ w hstar hturn g hgs hg hbase _ hdense
    (B.union_turnCenter_stable D P ι hp ht)
    (B.limit_reduced_moment D P ι hp ht ψ w F hFb hFw hdir g hFg) hgen

end PeakingPairData

open Topology
namespace PeakingPairData
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A V C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra V] [PartialOrder V] [StarOrderedRing V]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

lemma HNNAmbientPresentation.directed_limit {I : Type*} [Nonempty I]
    (G : PeakingPairData A) (S T : I → Type)
    [∀ i, CStarAlgebra (S i)] [∀ i, PartialOrder (S i)] [∀ i, StarOrderedRing (S i)]
    [∀ i, CStarAlgebra (T i)]
    (v : V →⋆ₐ[ℂ] A) (s : ∀ i, S i →⋆ₐ[ℂ] A) (t : ∀ i, T i →⋆ₐ[ℂ] A)
    (c : C →⋆ₐ[ℂ] A) (hv : Function.Injective v) (hc : Function.Injective c)
    (ι : ∀ i, S i →⋆ₐ[ℂ] V) (hι : ∀ i a, v (ι i a) = s i a)
    (φ : ∀ i, T i →⋆ₐ[ℂ] C) (hφ : ∀ i a, c (φ i a) = t i a)
    (ψ : V →⋆ₐ[ℂ] C) (hψ : ∀ a, c (ψ a) = v a)
    (w : Bool → C) (z : Bool → A) (hw : ∀ i, c (w i) = z i)
    (h : ∀ i, G.HNNAmbientPresentation (s i) (t i) z)
    (B : PeakingPairData V) (hp : ∀ i n, v (B.peak i n) = G.peak i n)
    (ht : ∀ a, B.trace a = G.trace (v a))
    (hdir : Directed (· ⊆ ·) (fun i => Set.range (ι i)))
    (hdense : Dense (⋃ i, Set.range (ι i)))
    (hgen : Dense (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C)) :
    G.HNNAmbientPresentation v c z := by
  choose P hpp hpt e heb hew het using h
  let F (i : I) : (P i).HNNAlgebra →⋆ₐ[ℂ] C := (φ i).comp (e i).toStarAlgHom
  have hFb (i : I) (a : S i) : F i ((P i).hnnBase a) = ψ (ι i a) := by
    apply hc
    exact (hφ i _).trans ((heb i a).trans ((hι i a).symm.trans (hψ _).symm))
  have hFw (i : I) (b : Bool) : F i ((P i).hnnLetter b) = w b := by
    apply hc
    exact (hφ i _).trans ((hew i b).trans (hw b).symm)
  have hpeak (i : I) (b : Bool) (n : ℕ) : ι i ((P i).peak b n) = B.peak b n := by
    apply hv
    exact (hι i _).trans ((hpp i b n).trans (hp b n).symm)
  have htrace (i : I) (a : S i) : B.trace (ι i a) = (P i).trace a := by
    rw [ht,hι,hpt]
  let g := restrictState c (positiveCLM G.trace)
  have hgs : IsState g := isState_restrict c _ (positiveCLM_isState G.trace G.normalized)
  have hgf (x : C) (he : g (star x*x) = 0) : x = 0 := by
    apply hc
    rw [map_zero]
    apply G.faithful
    change G.trace (c (star x*x)) = 0 at he
    simpa only [map_mul,map_star] using he
  have hFg (i : I) (b : (P i).HNNAlgebra) : g (F i b) = (P i).hnnTrace b := by
    change G.trace (c (φ i (e i b))) = _
    rw [hφ,het]
  obtain ⟨f,hfb,hfw,hft⟩ := B.hnn_directed_limit_presentation S P ι hpeak htrace ψ w F
    hFb hFw hdir hdense g hgs hgf hFg hgen
  refine ⟨B,hp,ht,f,?_,?_,hft⟩
  · intro a
    rw [hfb,hψ]
  · intro i
    rw [hfw,hw]

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] hnnGenerated_isClosed
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma AmbientPresentation.le (G : PeakingPairData A)
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] (hp : ∀ i n, G.peak i n ∈ S)
    (z : A) (T : StarSubalgebra ℂ A) [IsClosed (T : Set A)]
    (h : G.AmbientPresentation S hp z T)
    (U : StarSubalgebra ℂ A) [IsClosed (U : Set A)] (hSU : S ≤ U) (hz : z ∈ U) : T ≤ U := by
  rw [h.generated]
  change (StarAlgebra.adjoin ℂ _).topologicalClosure ≤ U
  apply StarSubalgebra.topologicalClosure_minimal _ (inferInstance : IsClosed (U : Set A))
  apply StarAlgebra.adjoin_le
  rintro x (⟨a,rfl⟩ | ⟨i,rfl⟩)
  · exact hSU a.property
  · cases i <;> simp only [starPair]
    · exact hz
    · exact star_mem hz

theorem ambient_presentation_directed_limit {I : Type*} [Nonempty I]
    (G : PeakingPairData A)
    (S T : I → StarSubalgebra ℂ A)
    [∀ i, IsClosed (S i : Set A)] [∀ i, IsClosed (T i : Set A)]
    (V : StarSubalgebra ℂ A) [IsClosed (V : Set A)]
    (pS : ∀ i s n, G.peak s n ∈ S i) (pV : ∀ s n, G.peak s n ∈ V)
    (hSV : ∀ i, S i ≤ V) (z : A)
    (h : ∀ i, G.AmbientPresentation (S i) (pS i) z (T i))
    (hdir : Directed (· ⊆ ·) (fun i => Set.range (StarSubalgebra.inclusion (hSV i))))
    (hdense : Dense (⋃ i, Set.range (StarSubalgebra.inclusion (hSV i)))) :
    G.AmbientPresentation V pV z (hnnGenerated V.subtype (starPair z)) := by
  classical
  let C := hnnGenerated V.subtype (starPair z)
  let B := G.onSubalgebra V pV
  let incl (i : I) : S i →⋆ₐ[ℂ] V := StarSubalgebra.inclusion (hSV i)
  let ψ : V →⋆ₐ[ℂ] C := hnnGeneratedBase V.subtype (starPair z)
  let w : Bool → C := hnnGeneratedLetter V.subtype (starPair z)
  have hVC : V ≤ C := by
    intro a ha
    exact (hnnGeneratedBase V.subtype (starPair z) ⟨a,ha⟩).property
  have hzC : z ∈ C := (hnnGeneratedLetter V.subtype (starPair z) false).property
  have hTC (i : I) : T i ≤ C := AmbientPresentation.le G (S i) (pS i) z (T i) (h i) C ((hSV i).trans hVC) hzC
  exact HNNAmbientPresentation.directed_limit G (fun i => S i) (fun i => T i)
    V.subtype (fun i => (S i).subtype) (fun i => (T i).subtype) C.subtype
    Subtype.val_injective Subtype.val_injective incl (fun _ _ => rfl)
    (fun i => StarSubalgebra.inclusion (hTC i)) (fun _ _ => rfl)
    ψ (fun _ => rfl) w (starPair z) (fun _ => rfl) h B
    (fun _ _ => rfl) (fun _ => rfl) hdir hdense (hnnGenerated_dense V.subtype (starPair z))

end PeakingPairData

open Topology
section
attribute [local irreducible] PeakingPairData.HNNAlgebra
universe u
variable {A : Type} [CStarAlgebra A]

def omittedIndices (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) : Set Ordinal.{u} :=
  Set.Iio j ∪ (S ∩ Set.Iio β)

lemma omittedIndices_mono (j : Ordinal.{u}) (S : Set Ordinal.{u}) :
    Monotone (omittedIndices j S) := by
  intro β γ h k hk
  rcases hk with hk | ⟨hk,hk'⟩
  · exact Or.inl hk
  · exact Or.inr ⟨hk,hk'.trans_le h⟩

lemma omittedIndices_zero (j : Ordinal.{u}) (S : Set Ordinal.{u}) :
    omittedIndices j S 0 = Set.Iio j := by
  ext k
  simp [omittedIndices]

lemma omittedIndices_succ (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u})
    (hk : k ∈ S) : omittedIndices j S (k+1) = insert k (omittedIndices j S k) := by
  ext x
  constructor
  · rintro (hx | ⟨hx,hx'⟩)
    · exact Or.inr (Or.inl hx)
    · rcases lt_or_eq_of_le (Order.lt_add_one_iff.mp (show x < k+1 from hx')) with hd | rfl
      · exact Or.inr (Or.inr ⟨hx,hd⟩)
      · exact Or.inl rfl
  · rintro (rfl | (hx | ⟨hx,hx'⟩))
    · exact Or.inr ⟨hk,show x < x+1 from Order.lt_succ x⟩
    · exact Or.inl hx
    · exact Or.inr ⟨hx,show x < k+1 from (show x < k from hx').trans_le le_self_add⟩

lemma omittedIndices_succ_of_not_mem (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u})
    (hk : k ∉ S) : omittedIndices j S (k+1) = omittedIndices j S k := by
  apply Set.Subset.antisymm
  · rintro x (hx | ⟨hx,hx'⟩)
    · exact Or.inl hx
    · right
      refine ⟨hx,show x < k from lt_of_le_of_ne (Order.lt_add_one_iff.mp (show x < k+1 from hx')) ?_⟩
      intro he; exact hk (he ▸ hx)
  · exact omittedIndices_mono j S le_self_add

lemma omittedIndices_succ_of_lt (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u})
    (hk : k < j) : omittedIndices j S (k+1) = omittedIndices j S k := by
  apply Set.Subset.antisymm
  · rintro x (hx | ⟨hx,hx'⟩)
    · exact Or.inl hx
    · exact Or.inl (lt_of_le_of_lt (Order.lt_add_one_iff.mp (show x < k+1 from hx')) hk)
  · exact omittedIndices_mono j S le_self_add

lemma omittedIndices_subset_Iio (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u})
    (hj : j ≤ k) : omittedIndices j S k ⊆ Set.Iio k := by
  rintro x (hx | ⟨_,hx⟩)
  · exact hx.trans_le hj
  · exact hx

lemma omittedIndices_insert_eq (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) :
    insert j (omittedIndices j S β) = omittedIndices (j+1) S β := by
  ext k
  constructor
  · rintro (rfl | (hk | hk))
    · exact Or.inl (show k < k+1 from Order.lt_succ k)
    · exact Or.inl (show k < j+1 from (show k < j from hk).trans_le le_self_add)
    · exact Or.inr hk
  · rintro (hk | hk)
    · rcases lt_or_eq_of_le (Order.lt_add_one_iff.mp (show k < j+1 from hk)) with hk | rfl
      · exact Or.inr (Or.inl hk)
      · exact Or.inl rfl
    · exact Or.inr (Or.inr hk)

lemma omittedIndices_iUnion (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u})
    (hβ : Order.IsSuccLimit β) :
    (⋃ k : {k : Ordinal.{u} // k < β}, omittedIndices j S k.val) = omittedIndices j S β := by
  have h0 : (0 : Ordinal.{u}) < β := hβ.ne_bot.bot_lt
  ext x
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    exact omittedIndices_mono j S k.property.le hk
  · rintro (hx | ⟨hx,hx'⟩)
    · exact Set.mem_iUnion.mpr ⟨⟨0,h0⟩,Or.inl hx⟩
    · exact Set.mem_iUnion.mpr ⟨⟨Order.succ x,hβ.succ_lt hx'⟩,
        Or.inr ⟨hx,Order.lt_succ x⟩⟩

def omittedAlgebra (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) : StarSubalgebra ℂ A :=
  generatedFamily base v (omittedIndices j S β)

instance omittedAlgebra_isClosed (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) :
    IsClosed (omittedAlgebra base v j S β : Set A) := generatedFamily_isClosed _ _ _

private noncomputable instance omittedAlgebra_cstar (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) :
    CStarAlgebra (omittedAlgebra base v j S β) := StarSubalgebra.cstarAlgebra _

lemma omittedAlgebra_mono (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) : Monotone (omittedAlgebra base v j S) :=
  (generatedFamily_mono base v).comp (omittedIndices_mono j S)

lemma omittedAlgebra_hnnGenerated (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) :
    hnnGenerated (omittedAlgebra base v j S β).subtype (starPair (v j)) =
      omittedAlgebra base v (j+1) S β := by
  rw [hnnGenerated_self]
  exact (generatedFamily_insert base v (omittedIndices j S β) j).symm.trans
    (congrArg (generatedFamily base v) (omittedIndices_insert_eq j S β))

lemma omittedAlgebra_continuous (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) (hβ : Order.IsSuccLimit β) :
    (omittedAlgebra base v j S β : Set A) =
      closure (⋃ k : {k : Ordinal.{u} // k < β}, (omittedAlgebra base v j S k.val : Set A)) := by
  let K := {k : Ordinal.{u} // k < β}
  let : Nonempty K := ⟨⟨0,hβ.ne_bot.bot_lt⟩⟩
  have hd : Directed (· ⊆ ·) (fun k : K => omittedIndices j S k.val) := by
    intro k l
    exact ⟨⟨max k.val l.val,max_lt k.property l.property⟩,
      omittedIndices_mono j S (le_max_left _ _),omittedIndices_mono j S (le_max_right _ _)⟩
  change (generatedFamily base v (omittedIndices j S β) : Set A) = _
  rw [← omittedIndices_iUnion j S β hβ]
  exact generatedFamily_iUnion_directed base v _ hd

lemma directed_starSubalgebra_ranges {I : Type*} [Preorder I] [IsDirectedOrder I]
    (S : I → StarSubalgebra ℂ A) (V : StarSubalgebra ℂ A)
    (hS : Monotone S) (hSV : ∀ i, S i ≤ V) :
    Directed (· ⊆ ·) (fun i => Set.range (StarSubalgebra.inclusion (hSV i))) := by
  intro i j
  obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
  refine ⟨k,?_,?_⟩
  · rintro a ⟨b,rfl⟩
    exact ⟨⟨b,hS hik b.property⟩,rfl⟩
  · rintro a ⟨b,rfl⟩
    exact ⟨⟨b,hS hjk b.property⟩,rfl⟩

end

open Topology
section
universe u
variable {A : Type} [CStarAlgebra A]

lemma hnnGenerated_eq_of_mem (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (z : A) (hz : z ∈ S) : hnnGenerated S.subtype (starPair z) = S := by
  rw [hnnGenerated_self]
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_minimal _ (inferInstance : IsClosed (S : Set A))
    apply StarAlgebra.adjoin_le
    rintro x (hx | hx)
    · exact hx
    · exact Set.mem_singleton_iff.mp hx ▸ hz
  · intro x hx
    exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl hx))

lemma omittedAlgebra_zero (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) :
    omittedAlgebra base v j S 0 = generatedFamily base v (Set.Iio j) :=
  congrArg (generatedFamily base v) (omittedIndices_zero j S)

lemma omittedAlgebra_base_mono (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (β : Ordinal.{u}) {i j : Ordinal.{u}} (hij : i ≤ j) :
    omittedAlgebra base v i S β ≤ omittedAlgebra base v j S β := by
  apply generatedFamily_mono
  apply Set.union_subset_union_left
  exact fun _ hx => (show _ < i from hx).trans_le hij

lemma omittedAlgebra_le_chronological (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) (hj : j ≤ β) :
    omittedAlgebra base v j S β ≤ generatedFamily base v (Set.Iio β) :=
  generatedFamily_mono base v (omittedIndices_subset_Iio j S β hj)

lemma omittedAlgebra_contains_initial (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) :
    generatedFamily base v (Set.Iio j) ≤ omittedAlgebra base v j S β :=
  generatedFamily_mono base v Set.subset_union_left

lemma omittedAlgebra_succ_of_not_mem (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u}) (hk : k ∉ S) :
    omittedAlgebra base v j S (k+1) = omittedAlgebra base v j S k :=
  congrArg (generatedFamily base v) (omittedIndices_succ_of_not_mem j S k hk)

lemma omittedAlgebra_succ_of_lt (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u}) (hk : k < j) :
    omittedAlgebra base v j S (k+1) = omittedAlgebra base v j S k :=
  congrArg (generatedFamily base v) (omittedIndices_succ_of_lt j S k hk)

lemma omittedAlgebra_succ (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u}) (hk : k ∈ S) :
    omittedAlgebra base v j S (k+1) =
      hnnGenerated (omittedAlgebra base v j S k).subtype (starPair (v k)) := by
  rw [hnnGenerated_self]
  exact (congrArg (generatedFamily base v) (omittedIndices_succ j S k hk)).trans
    (generatedFamily_insert base v (omittedIndices j S k) k)

lemma omittedAlgebra_succ_of_one (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u}) (hv : v k = 1) :
    omittedAlgebra base v j S (k+1) = omittedAlgebra base v j S k := by
  classical
  by_cases hk : k ∈ S
  · rw [omittedAlgebra_succ base v j S k hk]
    exact hnnGenerated_eq_of_mem _ _ (hv ▸ (omittedAlgebra base v j S k).one_mem)
  · exact omittedAlgebra_succ_of_not_mem base v j S k hk

end

open Topology
section
variable {A : Type*} [CStarAlgebra A]

lemma dense_subalgebra_inclusion_ranges {I : Type*}
    (S : I → StarSubalgebra ℂ A) (V : StarSubalgebra ℂ A) (hSV : ∀ i, S i ≤ V)
    (hcont : (V : Set A) = closure (⋃ i, (S i : Set A))) :
    Dense (⋃ i, Set.range (StarSubalgebra.inclusion (hSV i))) := by
  have he : (⋃ i, Set.range (StarSubalgebra.inclusion (hSV i))) =
      (Subtype.val : V → A) ⁻¹' (⋃ i, (S i : Set A)) := by
    ext a
    simp only [Set.mem_iUnion,Set.mem_range,Set.mem_preimage]
    constructor
    · rintro ⟨i,b,rfl⟩
      exact ⟨i,b.property⟩
    · rintro ⟨i,hi⟩
      exact ⟨i,⟨a,hi⟩,rfl⟩
  rw [he]
  intro a
  have hsub : (⋃ i, (S i : Set A)) ⊆ (V : Set A) := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact hSV i hi
  rw [closure_subtype]
  have himg : (Subtype.val : V → A) '' ((Subtype.val : V → A) ⁻¹' (⋃ i, (S i : Set A))) =
      ⋃ i, (S i : Set A) := by
    exact Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x,hsub hx⟩,rfl⟩)
  rw [himg]
  rw [← hcont]
  exact a.property

end

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] hnnGenerated_isClosed
variable {A : Type} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
lemma subalgebra_inclusion_ranges_directed [PartialOrder A] [StarOrderedRing A] (S : Ordinal.{u} → StarSubalgebra ℂ A)
    (hmono : Monotone S) (β : Ordinal.{u}) :
    Directed (· ⊆ ·) (fun k : Set.Iio β =>
      Set.range (StarSubalgebra.inclusion (hmono k.property.le))) := by
  intro k l
  let m : Set.Iio β := ⟨max k.val l.val,max_lt (show k.val < β from k.property) (show l.val < β from l.property)⟩
  refine ⟨m,?_,?_⟩
  · rintro a ⟨b,rfl⟩
    exact ⟨⟨b,hmono (le_max_left k.val l.val) b.property⟩,rfl⟩
  · rintro a ⟨b,rfl⟩
    exact ⟨⟨b,hmono (le_max_right k.val l.val) b.property⟩,rfl⟩

theorem ambient_presentation_ordinal_limit
    (P : PeakingPairData A) (S R : Ordinal.{u} → StarSubalgebra ℂ A)
    [∀ k, IsClosed (S k : Set A)] [∀ k, IsClosed (R k : Set A)]
    (pS : ∀ k i n, P.peak i n ∈ S k)
    (hmono : Monotone S) (z : A) (β : Ordinal.{u}) (hβ : 0 < β)
    (hcont : (S β : Set A) = closure (⋃ k : Set.Iio β, (S k.val : Set A)))
    (ih : ∀ k < β, P.AmbientPresentation (S k) (pS k) z (R k)) :
    P.AmbientPresentation (S β) (pS β) z (hnnGenerated (S β).subtype (starPair z)) := by
  let : Nonempty (Set.Iio β) := ⟨⟨0,hβ⟩⟩
  exact ambient_presentation_directed_limit P (fun k : Set.Iio β => S k.val)
    (fun k : Set.Iio β => R k.val) (S β) (fun k => pS k.val) (pS β)
    (fun k => hmono k.property.le) z (fun k => ih k.val k.property)
    (subalgebra_inclusion_ranges_directed S hmono β)
    (dense_subalgebra_inclusion_ranges (fun k : Set.Iio β => S k.val) (S β)
      (fun k => hmono k.property.le) hcont)

end PeakingPairData

open Topology
namespace PeakingPairData

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed hnnGenerated_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hj : j < δ)
    (hja : j ∈ active) (hjS : j ∉ S)
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (htrace : ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a)
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j < k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)

def OmittedModel (P : PeakingPairData A) (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) : Prop :=
  P.HNNAmbientPresentation (omittedAlgebra base v j S β).subtype
    (omittedAlgebra base v (j+1) S β).subtype (starPair (v j))

include hjS hpeak hchrono hinactive htrace hdep hja in
lemma omitted_model_successor (k : Ordinal.{u}) (hkδ : k < δ)
    (hi : (Q j).OmittedModel base v j S k) : (Q j).OmittedModel base v j S (k+1) := by
  let O := omittedAlgebra base v j S
  let R := omittedAlgebra base v (j+1) S
  let pO (β : Ordinal.{u}) (i : Bool) (n : ℕ) : (Q j).peak i n ∈ O β :=
    omittedAlgebra_contains_initial base v j S β (hpeak j hja i n)
  change (Q j).AmbientPresentation (O k) (pO k) (v j) (R k) at hi
  change (Q j).AmbientPresentation (O (k+1)) (pO (k+1)) (v j) (R (k+1))
  have inert (hO : O (k+1) = O k) (hR : R (k+1) = R k) :
      (Q j).AmbientPresentation (O (k+1)) (pO (k+1)) (v j) (R (k+1)) :=
    AmbientPresentation.congr (Q j) _ _ _ _ (pO k) (pO (k+1)) (v j) hO.symm hR.symm hi
  by_cases hkS : k ∈ S
  · by_cases hkj : k < j
    · exact inert (omittedAlgebra_succ_of_lt base v j S k hkj)
        (omittedAlgebra_succ_of_lt base v (j+1) S k (hkj.trans_le le_self_add))
    · have hjk : j < k := lt_of_le_of_ne (le_of_not_gt hkj) (fun e => hjS (e ▸ hkS))
      by_cases hka : k ∈ active
      · have qO := hdep k hkδ hkS hka hjk
        have hOR : O k ≤ R k := omittedAlgebra_base_mono base v S k le_self_add
        have qR : ∀ i n, (Q k).peak i n ∈ R k := fun i n => hOR (qO i n)
        have hOX : O k ≤ generatedFamily base v (Set.Iio k) :=
          omittedAlgebra_le_chronological base v j S k hjk.le
        have hRX : R k ≤ generatedFamily base v (Set.Iio k) :=
          omittedAlgebra_le_chronological base v (j+1) S k (Order.add_one_le_iff.mpr hjk)
        have Hq := ambient_presentation_inherited (Q k) _ _ (O k)
          (hpeak k hka) qO (v k) hOX (hchrono k hkδ hka)
        have Hr := ambient_presentation_inherited (Q k) _ _ (R k)
          (hpeak k hka) qR (v k) hRX (hchrono k hkδ hka)
        have Hq' := AmbientPresentation.congr (Q k) _ _ _ _ qO qO (v k) rfl
          (omittedAlgebra_succ base v j S k hkS).symm Hq
        have Hr' := AmbientPresentation.congr (Q k) _ _ _ _ qR qR (v k) rfl
          (omittedAlgebra_succ base v (j+1) S k hkS).symm Hr
        exact ambient_presentation_swap (Q j) (Q k) (O k) (R k) (O (k+1)) (R (k+1))
          (omittedAlgebra_base_mono base v S (k+1) le_self_add)
          (pO k) qO (pO (k+1)) qR (v j) (v k) (htrace k hkδ) hi Hq' Hr'
      · exact inert (omittedAlgebra_succ_of_one base v j S k (hinactive k hkδ hka))
          (omittedAlgebra_succ_of_one base v (j+1) S k (hinactive k hkδ hka))
  · exact inert (omittedAlgebra_succ_of_not_mem base v j S k hkS)
      (omittedAlgebra_succ_of_not_mem base v (j+1) S k hkS)

include hpeak hja in
lemma omitted_model_limit (β : Ordinal.{u}) (hlim : Order.IsSuccLimit β)
    (ih : ∀ k < β, (Q j).OmittedModel base v j S k) :
    (Q j).OmittedModel base v j S β := by
  let O := omittedAlgebra base v j S
  let R := omittedAlgebra base v (j+1) S
  let pO (β : Ordinal.{u}) (i : Bool) (n : ℕ) : (Q j).peak i n ∈ O β :=
    omittedAlgebra_contains_initial base v j S β (hpeak j hja i n)
  change (Q j).AmbientPresentation (O β) (pO β) (v j) (R β)
  have H := ambient_presentation_ordinal_limit (Q j) O R pO
    (fun _ _ h => omittedAlgebra_mono base v j S h) (v j) β hlim.ne_bot.bot_lt
    (omittedAlgebra_continuous base v j S β hlim) ih
  exact AmbientPresentation.congr (Q j) _ _ _ _ (pO β) (pO β) (v j) rfl
    (omittedAlgebra_hnnGenerated base v j S β) H

include hj hja hpeak hchrono in
lemma omitted_model_zero : (Q j).OmittedModel base v j S 0 := by
  exact AmbientPresentation.congr (Q j) _ _ _ _ (hpeak j hja)
    (fun i n => omittedAlgebra_contains_initial base v j S 0 (hpeak j hja i n)) (v j)
    (omittedAlgebra_zero base v j S).symm
    (omittedAlgebra_zero base v (j+1) S).symm (hchrono j hj hja)

private lemma ordinal_invariant (F : Ordinal.{u} → Prop) (δ : Ordinal.{u})
    (h0 : F 0) (hs : ∀ k < δ, F k → F (k+1))
    (hl : ∀ β ≤ δ, Order.IsSuccLimit β → (∀ k < β, F k) → F β)
    (β : Ordinal.{u}) (hβ : β ≤ δ) : F β := by
  induction β using Ordinal.limitRecOn with
  | zero => exact h0
  | add_one k ih =>
    have hk : k < δ := (Order.lt_succ k).trans_le hβ
    exact hs k hk (ih hk.le)
  | limit β hlim ih => exact hl β hβ hlim (fun k hk => ih k hk (hk.le.trans hβ))

include hj hja hjS hpeak hchrono hinactive htrace hdep in

theorem omitted_presentation_of_chronological (β : Ordinal.{u}) (hβ : β ≤ δ) :
    (Q j).AmbientPresentation (omittedAlgebra base v j S β)
      (fun i n => omittedAlgebra_contains_initial base v j S β (hpeak j hja i n))
      (v j) (omittedAlgebra base v (j+1) S β) :=
  ordinal_invariant ((Q j).OmittedModel base v j S) δ
    (omitted_model_zero base v Q active S δ j hj hja hpeak hchrono)
    (omitted_model_successor base v Q active S δ j hja hjS hpeak hchrono hinactive htrace hdep)
    (fun β _ hlim ih => omitted_model_limit base v Q active S j hja hpeak β hlim ih)
    β hβ

end

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A S T : Type}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra T] [partialOrderT : PartialOrder T] [starOrderedRingT : StarOrderedRing T]

lemma states_eq_of_ambient_peaks (G : PeakingPairData A)
    (B E : PeakingPairData S) (b : S →⋆ₐ[ℂ] A)
    (hpB : ∀ i n, b (B.peak i n) = G.peak i n)
    (hpE : ∀ i n, b (E.peak i n) = G.peak i n) (i : Bool) : B.state i = E.state i :=
  (B.state_natural G b hpB i).symm.trans (E.state_natural G b hpE i)

omit partialOrderT starOrderedRingT in
lemma HNNAmbientPresentation.bridge [PartialOrder T] [StarOrderedRing T] (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (ht : Function.Injective t) (ψ : S →⋆ₐ[ℂ] T) (hψ : ∀ a, t (ψ a) = b a)
    (h : G.HNNAmbientPresentation b t z) (E : PeakingPairData S)
    (hpE : ∀ i n, b (E.peak i n) = G.peak i n)
    (hne : ¬ PureStateEquivalent (E.state false) (E.peaks false).isPureState
      (E.state true) (E.peaks true).isPureState) : BridgeSuccessor ψ := by
  obtain ⟨B,hpB,_,e,heb,_,_⟩ := h
  have hnB : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState := by
    simpa only [states_eq_of_ambient_peaks G B E b hpB hpE] using hne
  refine BridgeSuccessor.hnn B (B.separated_of_inequivalent hnB) e (fun a => ?_)
  exact ht ((heb a).trans (hψ a).symm)

lemma HNNAmbientPresentation.no_unintended_join (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (ht : Function.Injective t) (ψ : S →⋆ₐ[ℂ] T) (hψ : ∀ a, t (ψ a) = b a)
    (h : G.HNNAmbientPresentation b t z) (E : PeakingPairData S)
    (hpE : ∀ i n, b (E.peak i n) = G.peak i n)
    (hE : ¬ PureStateEquivalent (E.state false) (E.peaks false).isPureState
      (E.state true) (E.peaks true).isPureState) (hS : IsSimpleCStar S)
    (f g : S →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (hne : ¬ PureStateEquivalent f hf g hg)
    (hex : ∀ i, ¬ (PureStateEquivalent f hf (E.state i) (E.peaks i).isPureState ∧
      PureStateEquivalent g hg (E.state (!i)) (E.peaks (!i)).isPureState))
    (F H : T →L[ℂ] ℂ) (hF : IsPureState F) (hH : IsPureState H)
    (hrF : restrictState ψ F = f) (hrH : restrictState ψ H = g) :
    ¬ PureStateEquivalent F hF H hH := by
  obtain ⟨B,hpB,_,e,heb,_,_⟩ := h
  have hs (i : Bool) := states_eq_of_ambient_peaks G B E b hpB hpE i
  have hnB : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState := by
    simpa only [hs] using hE
  have hexB : ∀ i, ¬ (PureStateEquivalent f hf (B.state i) (B.peaks i).isPureState ∧
      PureStateEquivalent g hg (B.state (!i)) (B.peaks (!i)).isPureState) := by
    simpa only [hs] using hex
  have heψ : e.toStarAlgHom.comp B.hnnBase = ψ := by
    ext a
    exact ht ((heb a).trans (hψ a).symm)
  have hRF : restrictState B.hnnBase (restrictState e.toStarAlgHom F) = f := by
    rw [restrictState_comp,heψ,hrF]
  have hRH : restrictState B.hnnBase (restrictState e.toStarAlgHom H) = g := by
    rw [restrictState_comp,heψ,hrH]
  intro he
  exact B.hnn_no_unintended_join (B.separated_of_inequivalent hnB) hS
    f g hf hg hne hexB _ _ (isPureState_restrict_equiv e F hF)
    (isPureState_restrict_equiv e H hH) hRF hRH
    (pureStateEquivalent_restrict_equiv e F H hF hH he)

end

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma onSubalgebra_class_exclusions (P Q : PeakingPairData A)
    (S X : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (X : Set A)]
    (pS : ∀ i n, P.peak i n ∈ S) (qS : ∀ i n, Q.peak i n ∈ S)
    (pX : ∀ i n, P.peak i n ∈ X) (qX : ∀ i n, Q.peak i n ∈ X)
    (hSX : S ≤ X)
    (hjoin : PureStateEquivalent ((P.onSubalgebra X pX).state false)
      ((P.onSubalgebra X pX).peaks false).isPureState ((P.onSubalgebra X pX).state true)
      ((P.onSubalgebra X pX).peaks true).isPureState)
    (hne : ¬ PureStateEquivalent ((Q.onSubalgebra X qX).state false)
      ((Q.onSubalgebra X qX).peaks false).isPureState ((Q.onSubalgebra X qX).state true)
      ((Q.onSubalgebra X qX).peaks true).isPureState) :
    (¬ PureStateEquivalent ((Q.onSubalgebra S qS).state false)
      ((Q.onSubalgebra S qS).peaks false).isPureState ((Q.onSubalgebra S qS).state true)
      ((Q.onSubalgebra S qS).peaks true).isPureState) ∧
    ∀ i, ¬ (PureStateEquivalent ((P.onSubalgebra S pS).state false)
        ((P.onSubalgebra S pS).peaks false).isPureState ((Q.onSubalgebra S qS).state i)
        ((Q.onSubalgebra S qS).peaks i).isPureState ∧
      PureStateEquivalent ((P.onSubalgebra S pS).state true)
        ((P.onSubalgebra S pS).peaks true).isPureState ((Q.onSubalgebra S qS).state (!i))
        ((Q.onSubalgebra S qS).peaks (!i)).isPureState) := by
  refine ⟨Q.onSubalgebra_inequivalent_of_larger S qS X hSX qX hne,?_⟩
  intro i he
  have lift (a b : Bool) (hab : PureStateEquivalent ((P.onSubalgebra S pS).state a)
      ((P.onSubalgebra S pS).peaks a).isPureState ((Q.onSubalgebra S qS).state b)
      ((Q.onSubalgebra S qS).peaks b).isPureState) :
      PureStateEquivalent ((P.onSubalgebra X pX).state a)
        ((P.onSubalgebra X pX).peaks a).isPureState ((Q.onSubalgebra X qX).state b)
        ((Q.onSubalgebra X qX).peaks b).isPureState :=
    pure_lifts_equivalent (StarSubalgebra.inclusion hSX) _ _
      ((P.onSubalgebra S pS).peaks a).isPureState ((Q.onSubalgebra S qS).peaks b).isPureState
      hab (Q.onSubalgebra_unique_inclusion S qS X hSX qX b) _ _
      ((P.onSubalgebra X pX).peaks a).isPureState ((Q.onSubalgebra X qX).peaks b).isPureState
      rfl rfl
  have H := PureStateEquivalent.trans (PureStateEquivalent.symm (lift false i he.1))
    (PureStateEquivalent.trans hjoin (lift true (!i) he.2))
  cases i
  · exact hne H
  · exact hne (PureStateEquivalent.symm H)

theorem ambient_preserves_omitted_inequivalence (P Q : PeakingPairData A)
    (S T X : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    [IsClosed (X : Set A)] (hST : S ≤ T) (hSX : S ≤ X)
    (pS : ∀ i n, P.peak i n ∈ S) (qS : ∀ i n, Q.peak i n ∈ S)
    (pT : ∀ i n, P.peak i n ∈ T)
    (pX : ∀ i n, P.peak i n ∈ X) (qX : ∀ i n, Q.peak i n ∈ X)
    (z : A) (hQ : Q.AmbientPresentation S qS z T) (hs : IsSimpleCStar S)
    (hjoin : PureStateEquivalent ((P.onSubalgebra X pX).state false)
      ((P.onSubalgebra X pX).peaks false).isPureState ((P.onSubalgebra X pX).state true)
      ((P.onSubalgebra X pX).peaks true).isPureState)
    (hneQ : ¬ PureStateEquivalent ((Q.onSubalgebra X qX).state false)
      ((Q.onSubalgebra X qX).peaks false).isPureState ((Q.onSubalgebra X qX).state true)
      ((Q.onSubalgebra X qX).peaks true).isPureState)
    (hneP : ¬ PureStateEquivalent ((P.onSubalgebra S pS).state false)
      ((P.onSubalgebra S pS).peaks false).isPureState ((P.onSubalgebra S pS).state true)
      ((P.onSubalgebra S pS).peaks true).isPureState) :
    ¬ PureStateEquivalent ((P.onSubalgebra T pT).state false)
      ((P.onSubalgebra T pT).peaks false).isPureState ((P.onSubalgebra T pT).state true)
      ((P.onSubalgebra T pT).peaks true).isPureState := by
  obtain ⟨hne,hex⟩ := onSubalgebra_class_exclusions P Q S X pS qS pX qX hSX hjoin hneQ
  exact HNNAmbientPresentation.no_unintended_join Q S.subtype T.subtype (starPair z)
    Subtype.val_injective (StarSubalgebra.inclusion hST) (fun _ => rfl) hQ
    (Q.onSubalgebra S qS) (fun _ _ => rfl) hne hs _ _
    ((P.onSubalgebra S pS).peaks false).isPureState ((P.onSubalgebra S pS).peaks true).isPureState
    hneP hex _ _ ((P.onSubalgebra T pT).peaks false).isPureState
    ((P.onSubalgebra T pT).peaks true).isPureState rfl rfl

end

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
lemma ambient_identity_bridge [PartialOrder A] [StarOrderedRing A] (S T : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)] (hST : S ≤ T) (he : S = T) :
    BridgeSuccessor (StarSubalgebra.inclusion hST) := by
  subst T
  exact BridgeSuccessor.identity (StarAlgEquiv.refl ℂ S) (fun _ => rfl)

lemma AmbientPresentation.bridge (G : PeakingPairData A)
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    (pS : ∀ i n, G.peak i n ∈ S) (z : A) (hST : S ≤ T)
    (h : G.AmbientPresentation S pS z T)
    (hne : ¬ PureStateEquivalent ((G.onSubalgebra S pS).state false)
      ((G.onSubalgebra S pS).peaks false).isPureState ((G.onSubalgebra S pS).state true)
      ((G.onSubalgebra S pS).peaks true).isPureState) :
    BridgeSuccessor (StarSubalgebra.inclusion hST) :=
  HNNAmbientPresentation.bridge G S.subtype T.subtype (starPair z)
    Subtype.val_injective (StarSubalgebra.inclusion hST) (fun _ => rfl) h
    (G.onSubalgebra S pS) (fun _ _ => rfl) hne

end

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed hnnGenerated_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma omitted_active_bridge
    (base : Set A) (v : Ordinal.{u} → A) (Q : PeakingPairData A)
    (j k : Ordinal.{u}) (S : Set Ordinal.{u}) (hkS : k ∈ S) (hjk : j ≤ k)
    (qO : ∀ i n, Q.peak i n ∈ omittedAlgebra base v j S k)
    (qX : ∀ i n, Q.peak i n ∈ generatedFamily base v (Set.Iio k))
    (hQ : Q.AmbientPresentation (generatedFamily base v (Set.Iio k)) qX
      (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hneQ : ¬ PureStateEquivalent ((Q.onSubalgebra (generatedFamily base v (Set.Iio k)) qX).state false)
      ((Q.onSubalgebra (generatedFamily base v (Set.Iio k)) qX).peaks false).isPureState
      ((Q.onSubalgebra (generatedFamily base v (Set.Iio k)) qX).state true)
      ((Q.onSubalgebra (generatedFamily base v (Set.Iio k)) qX).peaks true).isPureState) :
    BridgeSuccessor (StarSubalgebra.inclusion
      (omittedAlgebra_mono base v j S (show k ≤ k+1 from le_self_add))) := by
  let O := omittedAlgebra base v j S
  let X := generatedFamily base v (Set.Iio k)
  have hOX : O k ≤ X := omittedAlgebra_le_chronological base v j S k hjk
  have Hp := ambient_presentation_inherited Q X _ (O k) qX qO (v k) hOX hQ
  have Hp' := AmbientPresentation.congr Q _ _ _ _ qO qO (v k) rfl
    (omittedAlgebra_succ base v j S k hkS).symm Hp
  exact AmbientPresentation.bridge Q (O k) (O (k+1)) qO (v k)
    (omittedAlgebra_mono base v j S le_self_add) Hp'
    (Q.onSubalgebra_inequivalent_of_larger (O k) qO X hOX qX hneQ)

theorem omitted_successor_bridge
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hjS : j ∉ S)
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      ¬ PureStateEquivalent (((Q k).onSubalgebra (generatedFamily base v (Set.Iio k)) (hpeak k hk)).state false)
        (((Q k).onSubalgebra (generatedFamily base v (Set.Iio k)) (hpeak k hk)).peaks false).isPureState
        (((Q k).onSubalgebra (generatedFamily base v (Set.Iio k)) (hpeak k hk)).state true)
        (((Q k).onSubalgebra (generatedFamily base v (Set.Iio k)) (hpeak k hk)).peaks true).isPureState)
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j < k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (k : Ordinal.{u}) (hkδ : k < δ) :
    BridgeSuccessor (StarSubalgebra.inclusion
      (omittedAlgebra_mono base v j S (show k ≤ k+1 from le_self_add))) := by
  have inert (he : omittedAlgebra base v j S (k+1) = omittedAlgebra base v j S k) :=
    ambient_identity_bridge _ _ (omittedAlgebra_mono base v j S le_self_add) he.symm
  by_cases hkS : k ∈ S
  · by_cases hkj : k < j
    · exact inert (omittedAlgebra_succ_of_lt base v j S k hkj)
    · have hjk : j < k := lt_of_le_of_ne (le_of_not_gt hkj) (fun e => hjS (e ▸ hkS))
      by_cases hka : k ∈ active
      · exact omitted_active_bridge base v (Q k) j k S hkS hjk.le
          (hdep k hkδ hkS hka hjk) (hpeak k hka) (hchrono k hkδ hka) (hne k hkδ hka)
      · exact inert (omittedAlgebra_succ_of_one base v j S k (hinactive k hkδ hka))
  · exact inert (omittedAlgebra_succ_of_not_mem base v j S k hkS)

end

end PeakingPairData

open Topology
namespace PeakingPairData

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
lemma subalgebra_simple_congr [PartialOrder A] [StarOrderedRing A] (S T : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)] (h : S = T) :
    IsSimpleCStar S ↔ IsSimpleCStar T := by subst T; rfl

omit partialOrderA starOrderedRingA in
theorem ambient_bridge_ordinal_simple [PartialOrder A] [StarOrderedRing A]
    (C : Ordinal.{u} → StarSubalgebra ℂ A) [∀ i, IsClosed (C i : Set A)]
    (hm : Monotone C) (L : Ordinal.{u}) (h0 : IsSimpleCStar (C 0))
    (hn : ∀ i < L, BridgeSuccessor (StarSubalgebra.inclusion (hm (show i ≤ i+1 from le_self_add))))
    (hc : ∀ k ≤ L, Order.IsSuccLimit k →
      (C k : Set A) = closure (⋃ i : {i : Ordinal.{u} // i < k}, (C i.val : Set A)))
    (k : Ordinal.{u}) (hk : k ≤ L) : IsSimpleCStar (C k) :=
  bridge_ordinal_simple (fun i => C i)
    (fun {_ _} h => StarSubalgebra.inclusion (hm h)) L h0 hn
    (fun h => StarSubalgebra.inclusion_injective (hm h))
    (fun k hk hl => dense_subalgebra_inclusion_ranges _ _ _ (hc k hk hl)) k hk

omit partialOrderA starOrderedRingA in
theorem ambient_bridge_ordinal_pureUEP [PartialOrder A] [StarOrderedRing A]
    (C : Ordinal.{u} → StarSubalgebra ℂ A) [∀ i, IsClosed (C i : Set A)]
    (hm : Monotone C) (L : Ordinal.{u}) (h0 : IsSimpleCStar (C 0))
    (hn : ∀ i < L, BridgeSuccessor (StarSubalgebra.inclusion (hm (show i ≤ i+1 from le_self_add))))
    (hc : ∀ k ≤ L, Order.IsSuccLimit k →
      (C k : Set A) = closure (⋃ i : {i : Ordinal.{u} // i < k}, (C i.val : Set A)))
    (k : Ordinal.{u}) (hk : k ≤ L) (i : Ordinal.{u}) (hik : i ≤ k) :
    PureUEP (StarSubalgebra.inclusion (hm hik)) :=
  bridge_ordinal_pureUEP (fun k => C k)
    (fun {_ _} h => StarSubalgebra.inclusion (hm h)) L h0 hn
    (fun h => StarSubalgebra.inclusion_injective (hm h))
    (fun k hk hl => dense_subalgebra_inclusion_ranges _ _ _ (hc k hk hl))
    (fun _ => rfl) (fun _ _ => rfl) k hk i hik

end

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A S T : Type}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]

lemma joined_of_conjugacy (E : PeakingPairData T) (u : unitary T)
    (hc : ∀ n, (u:T)*E.peak false n*star (u:T) = E.peak true n) :
    PureStateEquivalent (E.state false) (E.peaks false).isPureState
      (E.state true) (E.peaks true).isPureState :=
  (E.peaks false).join_named (E.peaks true) (StarAlgHom.id ℂ T) u hc
    (StateExtensionUnique.of_surjective _ Function.surjective_id _)
    _ _ (E.peaks false).isPureState (E.peaks true).isPureState rfl rfl

lemma HNNAmbientPresentation.joined (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (ht : Function.Injective t) (h : G.HNNAmbientPresentation b t z)
    (E : PeakingPairData T) (hpE : ∀ i n, t (E.peak i n) = G.peak i n) :
    PureStateEquivalent (E.state false) (E.peaks false).isPureState
      (E.state true) (E.peaks true).isPureState := by
  obtain ⟨B,hpB,_,e,heb,_,_⟩ := h
  let u : unitary T := ⟨e (B.hnnUnitary:B.HNNAlgebra),by
    constructor
    · rw [← map_star,← map_mul,B.hnnUnitary.property.1,map_one]
    · rw [← map_star,← map_mul,B.hnnUnitary.property.2,map_one]⟩
  apply E.joined_of_conjugacy u
  have he (i : Bool) (n : ℕ) : e (B.hnnBase (B.peak i n)) = E.peak i n :=
    ht ((heb _).trans ((hpB i n).trans (hpE i n).symm))
  intro n
  change e (B.hnnUnitary:B.HNNAlgebra) * E.peak false n *
    star (e (B.hnnUnitary:B.HNNAlgebra)) = E.peak true n
  rw [← he false n,← he true n,← map_star,← map_mul,← map_mul,B.hnnUnitary_conjugates]

lemma AmbientPresentation.joined (G : PeakingPairData A)
    (V W : StarSubalgebra ℂ A) [IsClosed (V : Set A)] [IsClosed (W : Set A)]
    (pV : ∀ i n, G.peak i n ∈ V) (pW : ∀ i n, G.peak i n ∈ W)
    (z : A) (h : G.AmbientPresentation V pV z W) :
    PureStateEquivalent ((G.onSubalgebra W pW).state false)
      ((G.onSubalgebra W pW).peaks false).isPureState ((G.onSubalgebra W pW).state true)
      ((G.onSubalgebra W pW).peaks true).isPureState :=
  HNNAmbientPresentation.joined G V.subtype W.subtype (starPair z) Subtype.val_injective h
    (G.onSubalgebra W pW) (fun _ _ => rfl)

lemma joined_onSubalgebra_larger (G : PeakingPairData A)
    (V W : StarSubalgebra ℂ A) [IsClosed (V : Set A)] [IsClosed (W : Set A)]
    (pV : ∀ i n, G.peak i n ∈ V) (pW : ∀ i n, G.peak i n ∈ W) (hVW : V ≤ W)
    (h : PureStateEquivalent ((G.onSubalgebra V pV).state false)
      ((G.onSubalgebra V pV).peaks false).isPureState ((G.onSubalgebra V pV).state true)
      ((G.onSubalgebra V pV).peaks true).isPureState) :
    PureStateEquivalent ((G.onSubalgebra W pW).state false)
      ((G.onSubalgebra W pW).peaks false).isPureState ((G.onSubalgebra W pW).state true)
      ((G.onSubalgebra W pW).peaks true).isPureState :=
  pure_lifts_equivalent (StarSubalgebra.inclusion hVW) _ _
    ((G.onSubalgebra V pV).peaks false).isPureState ((G.onSubalgebra V pV).peaks true).isPureState
    h (G.onSubalgebra_unique_inclusion V pV W hVW pW true) _ _
    ((G.onSubalgebra W pW).peaks false).isPureState ((G.onSubalgebra W pW).peaks true).isPureState rfl rfl

end

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def PairDistinctOn (G : PeakingPairData A) (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (hp : ∀ i n, G.peak i n ∈ S) : Prop :=
  ¬ PureStateEquivalent ((G.onSubalgebra S hp).state false)
    ((G.onSubalgebra S hp).peaks false).isPureState ((G.onSubalgebra S hp).state true)
    ((G.onSubalgebra S hp).peaks true).isPureState

lemma PairDistinctOn.congr (G : PeakingPairData A)
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    (pS : ∀ i n, G.peak i n ∈ S) (pT : ∀ i n, G.peak i n ∈ T)
    (he : S = T) (h : G.PairDistinctOn S pS) : G.PairDistinctOn T pT := by
  subst T
  exact h

end

end PeakingPairData

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem inherited_successor_bridge
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u})
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j ≤ k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (k : Ordinal.{u}) (hkδ : k < δ) :
    BridgeSuccessor (StarSubalgebra.inclusion
      (omittedAlgebra_mono base v j S (show k ≤ k+1 from le_self_add))) := by
  have inert (he : omittedAlgebra base v j S (k+1) = omittedAlgebra base v j S k) :=
    ambient_identity_bridge _ _ (omittedAlgebra_mono base v j S le_self_add) he.symm
  by_cases hkS : k ∈ S
  · by_cases hkj : k < j
    · exact inert (omittedAlgebra_succ_of_lt base v j S k hkj)
    · have hjk : j ≤ k := le_of_not_gt hkj
      by_cases hka : k ∈ active
      · exact omitted_active_bridge base v (Q k) j k S hkS hjk
          (hdep k hkδ hkS hka hjk) (hpeak k hka) (hchrono k hkδ hka) (hne k hkδ hka)
      · exact inert (omittedAlgebra_succ_of_one base v j S k (hinactive k hkδ hka))
  · exact inert (omittedAlgebra_succ_of_not_mem base v j S k hkS)

theorem inherited_simple
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u})
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j ≤ k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio j)))
    (β : Ordinal.{u}) (hβ : β ≤ δ) : IsSimpleCStar (omittedAlgebra base v j S β) := by
  apply ambient_bridge_ordinal_simple (omittedAlgebra base v j S)
    (fun _ _ h => omittedAlgebra_mono base v j S h) δ _ _ _ β hβ
  · exact (subalgebra_simple_congr _ _ (omittedAlgebra_zero base v j S)).mpr h0
  · exact inherited_successor_bridge base v Q active S δ j hpeak hchrono hinactive hne hdep
  · intro k _ hlim
    exact omittedAlgebra_continuous base v j S k hlim

lemma dependency_peaks_omitted
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (I : Ordinal.{u} → Set Ordinal.{u}) (S : Set Ordinal.{u})
    (hclosed : DependencyClosed I S)
    (k j : Ordinal.{u}) (hkS : k ∈ S) (hI : I k ⊆ Set.Iio k)
    (hp : ∀ i n, (Q k).peak i n ∈ generatedFamily base v (I k)) :
    ∀ i n, (Q k).peak i n ∈ omittedAlgebra base v j S k := by
  intro i n
  exact generatedFamily_mono base v (fun x hx => Or.inr ⟨hclosed k hkS hx,hI hx⟩) (hp i n)

end PeakingPairData

section
open Topology
universe u
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

lemma omittedAlgebra_all_before (base : Set A) (v : Ordinal.{u} → A)
    (δ k : Ordinal.{u}) (hk : k ≤ δ) :
    omittedAlgebra base v 0 (Set.Iio δ) k = generatedFamily base v (Set.Iio k) := by
  apply congrArg (generatedFamily base v)
  ext x
  simp only [omittedIndices,Set.mem_union,Set.mem_Iio,not_lt_zero,false_or,Set.mem_inter_iff]
  exact ⟨And.right,fun hx => ⟨hx.trans_le hk,hx⟩⟩

lemma omittedAlgebra_endpoint_eq_retained (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hS : S ⊆ Set.Iio δ) :
    omittedAlgebra base v j S δ = retainedOrdinalAlgebra base v S j := by
  apply congrArg (generatedFamily base v)
  ext x
  constructor
  · rintro (hx | ⟨hx,_⟩)
    · exact Or.inr hx
    · exact Or.inl hx
  · rintro (hx | hx)
    · exact Or.inr ⟨hx,hS hx⟩
    · exact Or.inl hx

lemma retainedOrdinal_succ_generated (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (j : Ordinal.{u}) :
    retainedOrdinalAlgebra base v S (j+1) =
      hnnGenerated (retainedOrdinalAlgebra base v S j).subtype (starPair (v j)) := by
  change generatedFamily base v (S ∪ Set.Iio (j+1)) =
    hnnGenerated (generatedFamily base v (S ∪ Set.Iio j)).subtype (starPair (v j))
  rw [hnnGenerated_eq_insert]
  apply congrArg (generatedFamily base v)
  ext x
  constructor
  · rintro (hx | hx)
    · exact Or.inr (Or.inl hx)
    · rcases lt_or_eq_of_le (Order.lt_add_one_iff.mp (show x < j+1 from hx)) with hx | rfl
      · exact Or.inr (Or.inr hx)
      · exact Or.inl rfl
  · rintro (rfl | (hx | hx))
    · exact Or.inr (show x < x+1 from Order.lt_succ x)
    · exact Or.inl hx
    · exact Or.inr (show x < j+1 from (show x < j from hx).trans_le le_self_add)

lemma retainedOrdinal_succ_of_one (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (j : Ordinal.{u}) (hv : v j = 1) :
    retainedOrdinalAlgebra base v S (j+1) = retainedOrdinalAlgebra base v S j := by
  rw [retainedOrdinal_succ_generated]
  exact hnnGenerated_eq_of_mem _ _ (hv ▸ (retainedOrdinalAlgebra base v S j).one_mem)

lemma retainedOrdinal_endpoint (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (δ : Ordinal.{u}) (hS : S ⊆ Set.Iio δ) :
    retainedOrdinalAlgebra base v S δ = generatedFamily base v (Set.Iio δ) := by
  apply congrArg (generatedFamily base v)
  exact Set.union_eq_right.mpr hS

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
lemma ambient_bridge_congr [PartialOrder A] [StarOrderedRing A] (S T S' T' : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    [IsClosed (S' : Set A)] [IsClosed (T' : Set A)]
    (hST : S ≤ T) (hST' : S' ≤ T') (hS : S = S') (hT : T = T')
    (h : BridgeSuccessor (StarSubalgebra.inclusion hST)) :
    BridgeSuccessor (StarSubalgebra.inclusion hST') := by
  subst S'
  subst T'
  exact h

theorem chronological_simple
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active : Set Ordinal.{u}) (δ : Ordinal.{u})
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio 0)))
    (β : Ordinal.{u}) (hβ : β ≤ δ) : IsSimpleCStar (generatedFamily base v (Set.Iio β)) := by
  have hd : ∀ k < δ, k ∈ Set.Iio δ → k ∈ active → (0 : Ordinal.{u}) ≤ k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v 0 (Set.Iio δ) k := by
    intro k hk _ hka _ i n
    rw [omittedAlgebra_all_before base v δ k hk.le]
    exact hpeak k hka i n
  exact (subalgebra_simple_congr _ _ (omittedAlgebra_all_before base v δ β hβ)).mp
    (inherited_simple base v Q active (Set.Iio δ) δ 0 hpeak hchrono hinactive hne hd h0 β hβ)

end PeakingPairData
end

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem omitted_simple_of_chronological
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hjS : j ∉ S)
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j < k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio j)))
    (β : Ordinal.{u}) (hβ : β ≤ δ) : IsSimpleCStar (omittedAlgebra base v j S β) := by
  apply ambient_bridge_ordinal_simple (omittedAlgebra base v j S)
    (fun _ _ h => omittedAlgebra_mono base v j S h) δ _ _ _ β hβ
  · exact (subalgebra_simple_congr _ _ (omittedAlgebra_zero base v j S)).mpr h0
  · exact omitted_successor_bridge base v Q active S δ j hjS hpeak hchrono hinactive hne hdep
  · intro k _ hlim
    exact omittedAlgebra_continuous base v j S k hlim

end PeakingPairData

section
universe u
variable {A : Type} [CStarAlgebra A]

lemma generatedFamily_Iio_mono (base : Set A) (v : Ordinal.{u} → A) :
    Monotone (fun k : Ordinal.{u} => generatedFamily base v (Set.Iio k)) :=
  fun _ _ h => generatedFamily_mono base v (fun _ hk => hk.trans_le h)

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable [PartialOrder A] [StarOrderedRing A]

lemma chronological_joined (base : Set A) (v : Ordinal.{u} → A)
    (G : PeakingPairData A) (j k : Ordinal.{u}) (hjk : j < k)
    (p : ∀ i n, G.peak i n ∈ generatedFamily base v (Set.Iio j))
    (h : G.AmbientPresentation (generatedFamily base v (Set.Iio j)) p (v j)
      (generatedFamily base v (Set.Iio (j+1)))) :
    PureStateEquivalent
      ((G.onSubalgebra (generatedFamily base v (Set.Iio k))
        (fun i n => generatedFamily_Iio_mono base v hjk.le (p i n))).state false)
      ((G.onSubalgebra (generatedFamily base v (Set.Iio k))
        (fun i n => generatedFamily_Iio_mono base v hjk.le (p i n))).peaks false).isPureState
      ((G.onSubalgebra (generatedFamily base v (Set.Iio k))
        (fun i n => generatedFamily_Iio_mono base v hjk.le (p i n))).state true)
      ((G.onSubalgebra (generatedFamily base v (Set.Iio k))
        (fun i n => generatedFamily_Iio_mono base v hjk.le (p i n))).peaks true).isPureState := by
  let p' (i : Bool) (n : ℕ) := generatedFamily_Iio_mono base v
    (show j ≤ j+1 from le_self_add) (p i n)
  exact joined_onSubalgebra_larger G _ _ p' _
    (generatedFamily_Iio_mono base v (Order.add_one_le_iff.mpr hjk))
    (AmbientPresentation.joined G _ _ p p' (v j) h)

end PeakingPairData
end

open Topology
namespace PeakingPairData

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem ambient_pair_ordinal_inequivalent (G : PeakingPairData A)
    (C : Ordinal.{u} → StarSubalgebra ℂ A) [∀ i, IsClosed (C i : Set A)]
    (pC : ∀ k i n, G.peak i n ∈ C k) (hm : Monotone C) (L : Ordinal.{u})
    (h0 : G.PairDistinctOn (C 0) (pC 0))
    (hn : ∀ k < L, G.PairDistinctOn (C k) (pC k) → G.PairDistinctOn (C (k+1)) (pC (k+1)))
    (hc : ∀ k ≤ L, Order.IsSuccLimit k →
      (C k : Set A) = closure (⋃ i : {i : Ordinal.{u} // i < k}, (C i.val : Set A)))
    (k : Ordinal.{u}) (hk : k ≤ L) : G.PairDistinctOn (C k) (pC k) :=
  pure_inequivalent_ordinal_chain (fun k => C k)
    (fun {_ _} h => StarSubalgebra.inclusion (hm h)) (fun _ _ => rfl) L 0
    (fun k => (G.onSubalgebra (C k) (pC k)).state false)
    (fun k => (G.onSubalgebra (C k) (pC k)).state true)
    (fun k => ((G.onSubalgebra (C k) (pC k)).peaks false).isPureState)
    (fun k => ((G.onSubalgebra (C k) (pC k)).peaks true).isPureState)
    (fun _ => rfl) (fun _ => rfl) h0 (fun k hk _ => hn k hk)
    (fun k hk hl => dense_subalgebra_inclusion_ranges _ _ _ (hc k hk hl)) k hk bot_le

end

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed hnnGenerated_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma omitted_active_preserves_distinct
    (base : Set A) (v : Ordinal.{u} → A) (P Q : PeakingPairData A)
    (j k : Ordinal.{u}) (S : Set Ordinal.{u}) (hkS : k ∈ S) (hjk : j < k)
    (p : ∀ i n, P.peak i n ∈ generatedFamily base v (Set.Iio j))
    (qO : ∀ i n, Q.peak i n ∈ omittedAlgebra base v j S k)
    (qX : ∀ i n, Q.peak i n ∈ generatedFamily base v (Set.Iio k))
    (hP : P.AmbientPresentation (generatedFamily base v (Set.Iio j)) p
      (v j) (generatedFamily base v (Set.Iio (j+1))))
    (hQ : Q.AmbientPresentation (generatedFamily base v (Set.Iio k)) qX
      (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hs : IsSimpleCStar (omittedAlgebra base v j S k))
    (hneQ : Q.PairDistinctOn (generatedFamily base v (Set.Iio k)) qX)
    (hneP : P.PairDistinctOn (omittedAlgebra base v j S k)
      (fun i n => omittedAlgebra_contains_initial base v j S k (p i n))) :
    P.PairDistinctOn (omittedAlgebra base v j S (k+1))
      (fun i n => omittedAlgebra_contains_initial base v j S (k+1) (p i n)) := by
  let O := omittedAlgebra base v j S
  let X := generatedFamily base v (Set.Iio k)
  let pO (β : Ordinal.{u}) (i : Bool) (n : ℕ) :=
    omittedAlgebra_contains_initial base v j S β (p i n)
  let pX (i : Bool) (n : ℕ) := generatedFamily_Iio_mono base v hjk.le (p i n)
  have hOX : O k ≤ X := omittedAlgebra_le_chronological base v j S k hjk.le
  have Hp := ambient_presentation_inherited Q X _ (O k) qX qO (v k) hOX hQ
  have Hp' := AmbientPresentation.congr Q _ _ _ _ qO qO (v k) rfl
    (omittedAlgebra_succ base v j S k hkS).symm Hp
  exact ambient_preserves_omitted_inequivalence P Q (O k) (O (k+1)) X
    (omittedAlgebra_mono base v j S le_self_add) hOX (pO k) qO (pO (k+1)) pX qX
    (v k) Hp' hs (chronological_joined base v P j k hjk p hP) hneQ hneP

variable
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hj : j < δ)
    (hja : j ∈ active) (hjS : j ∉ S)
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j < k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio j)))

include hj hja hjS hpeak hchrono hinactive hne hdep h0 in
lemma omitted_distinct_successor (k : Ordinal.{u}) (hkδ : k < δ)
    (hi : (Q j).PairDistinctOn (omittedAlgebra base v j S k)
      (fun i n => omittedAlgebra_contains_initial base v j S k (hpeak j hja i n))) :
    (Q j).PairDistinctOn (omittedAlgebra base v j S (k+1))
      (fun i n => omittedAlgebra_contains_initial base v j S (k+1) (hpeak j hja i n)) := by
  let O := omittedAlgebra base v j S
  let pO (β : Ordinal.{u}) (i : Bool) (n : ℕ) :=
    omittedAlgebra_contains_initial base v j S β (hpeak j hja i n)
  have inert (he : O (k+1) = O k) : (Q j).PairDistinctOn (O (k+1)) (pO (k+1)) :=
    PairDistinctOn.congr (Q j) _ _ (pO k) (pO (k+1)) he.symm hi
  by_cases hkS : k ∈ S
  · by_cases hkj : k < j
    · exact inert (omittedAlgebra_succ_of_lt base v j S k hkj)
    · have hjk : j < k := lt_of_le_of_ne (le_of_not_gt hkj) (fun e => hjS (e ▸ hkS))
      by_cases hka : k ∈ active
      · exact omitted_active_preserves_distinct base v (Q j) (Q k) j k S hkS hjk
          (hpeak j hja) (hdep k hkδ hkS hka hjk) (hpeak k hka)
          (hchrono j hj hja) (hchrono k hkδ hka)
          (omitted_simple_of_chronological base v Q active S δ j hjS hpeak hchrono
            hinactive hne hdep h0 k hkδ.le) (hne k hkδ hka) hi
      · exact inert (omittedAlgebra_succ_of_one base v j S k (hinactive k hkδ hka))
  · exact inert (omittedAlgebra_succ_of_not_mem base v j S k hkS)

end

end PeakingPairData

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hj : j < δ)
    (hja : j ∈ active) (hjS : j ∉ S)
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j < k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio j)))

include hj hja hjS hpeak hchrono hinactive hne hdep h0 in

theorem omitted_distinct_of_chronological (β : Ordinal.{u}) (hβ : β ≤ δ) :
    (Q j).PairDistinctOn (omittedAlgebra base v j S β)
      (fun i n => omittedAlgebra_contains_initial base v j S β (hpeak j hja i n)) := by
  apply ambient_pair_ordinal_inequivalent (Q j) (omittedAlgebra base v j S)
    (fun β i n => omittedAlgebra_contains_initial base v j S β (hpeak j hja i n))
    (fun _ _ h => omittedAlgebra_mono base v j S h) δ _ _ _ β hβ
  · exact PairDistinctOn.congr (Q j) _ _ (hpeak j hja) _
      (omittedAlgebra_zero base v j S).symm (hne j hj hja)
  · exact omitted_distinct_successor base v Q active S δ j hj hja hjS hpeak hchrono
      hinactive hne hdep h0
  · intro k _ hlim
    exact omittedAlgebra_continuous base v j S k hlim

include hj hja hjS hpeak hchrono hinactive hne hdep h0 in

theorem omitted_endpoint_bridge
    (htrace : ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a) :
    BridgeSuccessor (StarSubalgebra.inclusion
      (omittedAlgebra_base_mono base v S δ (show j ≤ j+1 from le_self_add))) := by
  exact AmbientPresentation.bridge (Q j) _ _
    (fun i n => omittedAlgebra_contains_initial base v j S δ (hpeak j hja i n)) (v j) _
    (omitted_presentation_of_chronological base v Q active S δ j hj hja hjS hpeak
      hchrono hinactive htrace hdep δ le_rfl)
    (omitted_distinct_of_chronological base v Q active S δ j hj hja hjS hpeak
      hchrono hinactive hne hdep h0 δ le_rfl)

end PeakingPairData

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (I : Ordinal.{u} → Set Ordinal.{u}) (δ : Ordinal.{u})
    (hS : S ⊆ Set.Iio δ) (hclosed : DependencyClosed I S)
    (hI : ∀ k < δ, k ∈ active → I k ⊆ Set.Iio k)
    (hdata : ∀ k < δ, k ∈ active → ∀ i n, (Q k).peak i n ∈ generatedFamily base v (I k))
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio 0)))

include hS hclosed hI hdata hpeak hchrono hinactive hne h0 in

theorem dependency_closed_retained_simple :
    IsSimpleCStar (retainedOrdinalAlgebra base v S 0) := by
  apply (subalgebra_simple_congr _ _
    (omittedAlgebra_endpoint_eq_retained base v S δ 0 hS)).mp
  apply inherited_simple base v Q active S δ 0 hpeak hchrono hinactive hne _ h0 δ le_rfl
  intro k hkδ hkS hka _
  exact dependency_peaks_omitted base v Q I S hclosed k 0 hkS (hI k hkδ hka) (hdata k hkδ hka)

include hS hclosed hI hdata hpeak hchrono hinactive hne h0 in

theorem dependency_closed_retained_successor
    (htrace : ∀ j < δ, ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a)
    (j : Ordinal.{u}) (hj : j < δ) :
    BridgeSuccessor (retainedOrdinalInclusion base v S (show j ≤ j+1 from le_self_add)) := by
  by_cases hjS : j ∈ S
  · exact retainedOrdinalSuccessor_identity base v S j hjS
  · by_cases hja : j ∈ active
    · have hp := omitted_endpoint_bridge base v Q active S δ j hj hja hjS hpeak hchrono
        hinactive hne
        (fun k hkδ hkS hka _ => dependency_peaks_omitted base v Q I S hclosed k j hkS
          (hI k hkδ hka) (hdata k hkδ hka))
        (chronological_simple base v Q active δ hpeak hchrono hinactive hne h0 j hj.le)
        (htrace j hj)
      exact ambient_bridge_congr _ _ _ _ _ _
        (omittedAlgebra_endpoint_eq_retained base v S δ j hS)
        (omittedAlgebra_endpoint_eq_retained base v S δ (j+1) hS) hp
    · exact ambient_identity_bridge _ _ _
        (retainedOrdinal_succ_of_one base v S j (hinactive j hj hja)).symm

include hS hclosed hI hdata hpeak hchrono hinactive hne h0 in

theorem dependency_closed_pureUEP
    (htrace : ∀ j < δ, ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a) :
    PureUEP (retainedOrdinalInclusion base v S (show 0 ≤ δ from bot_le)) := by
  apply retainedOrdinal_pureUEP base v S δ
    (dependency_closed_retained_simple base v Q active S I δ hS hclosed hI hdata hpeak
      hchrono hinactive hne h0)
  exact dependency_closed_retained_successor base v Q active S I δ hS hclosed hI hdata
    hpeak hchrono hinactive hne h0 htrace

end PeakingPairData

open Topology
section
universe u v
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

lemma generatedFamily_reindex {J : Type u} {K : Type v}
    (base : Set A) (z : K → A) (e : J → K) (S : Set J) :
    generatedFamily base (z ∘ e) S = generatedFamily base z (e '' S) := by
  unfold generatedFamily
  rw [Set.image_image]
  rfl

lemma generatedFamily_map {B : Type*} [CStarAlgebra B] {J : Type*}
    (base : Set A) (z : J → A) (S : Set J) (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) :
    (generatedFamily base z S).map φ = generatedFamily (φ '' base) (φ ∘ z) S := by
  rw [generatedFamily,← StarSubalgebra.topologicalClosure_map _ φ
    (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosedMap
    (NonUnitalStarAlgHom.isometry φ hφ).continuous,StarAlgHom.map_adjoin,generatedFamily]
  congr 2
  rw [Set.image_union,Set.image_image]
  rfl

lemma subalgebra_pureUEP_congr (S T S' T' : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    [IsClosed (S' : Set A)] [IsClosed (T' : Set A)]
    (hST : S ≤ T) (hST' : S' ≤ T') (hS : S = S') (hT : T = T')
    (h : PureUEP (StarSubalgebra.inclusion hST)) :
    PureUEP (StarSubalgebra.inclusion hST') := by
  subst S'
  subst T'
  exact h

lemma subalgebra_pureRestriction_congr (S T : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)] (hST : S = T)
    (f : A →L[ℂ] ℂ) (h : IsPureState (restrictState S.subtype f)) :
    IsPureState (restrictState T.subtype f) := by
  subst T
  exact h

lemma subalgebraSubtype_pureUEP_of_top
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    (hST : S ≤ T) (hT : T = ⊤) (h : PureUEP (StarSubalgebra.inclusion hST)) :
    PureUEP S.subtype := by
  let e : T ≃⋆ₐ[ℂ] A := StarAlgEquiv.ofBijective T.subtype
    ⟨Subtype.val_injective,fun a => ⟨⟨a,by rw [hT]; trivial⟩,rfl⟩⟩
  have he : e.toStarAlgHom.comp (StarSubalgebra.inclusion hST) = S.subtype := by ext a; rfl
  rw [← he]
  exact h.postcomp_equiv e

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable [PartialOrder A] [StarOrderedRing A]
variable
    (base : Set A) (z : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active : Set Ordinal.{u}) (I : Ordinal.{u} → Set Ordinal.{u}) (δ : Ordinal.{u})
    (hI : ∀ k < δ, I k ⊆ Set.Iio k)
    (hdata : ∀ k < δ, k ∈ active → ∀ i n, (Q k).peak i n ∈ generatedFamily base z (I k))
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base z (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base z (Set.Iio k)) (hpeak k hk)
        (z k) (generatedFamily base z (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → z k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base z (Set.Iio k)) (hpeak k hk))
    (h0 : IsSimpleCStar (generatedFamily base z (Set.Iio 0)))
    (htrace : ∀ j < δ, ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a)

include hI hdata hpeak hchrono hinactive hne h0 htrace in
lemma literal_dependency_closed_pureUEP
    (S : Set Ordinal.{u}) (hS : S ⊆ Set.Iio δ) (hclosed : DependencyClosed I S) :
    PureUEP (StarSubalgebra.inclusion (generatedFamily_mono base z hS)) := by
  have hz : retainedOrdinalAlgebra base z S 0 = generatedFamily base z S := by
    change generatedFamily base z (S ∪ Set.Iio 0) = _
    rw [show Set.Iio (0:Ordinal.{u}) = ∅ by ext x; simp, Set.union_empty]
  exact subalgebra_pureUEP_congr _ _ _ _ _ _ hz
    (retainedOrdinal_endpoint base z S δ hS)
    (dependency_closed_pureUEP base z Q active S I δ hS hclosed
      (fun k hk _ => hI k hk) hdata hpeak hchrono hinactive hne h0 htrace)

include hI hdata hpeak hchrono hinactive hne h0 htrace in
lemma literal_dependency_closed_ambientUEP
    (hgen : generatedFamily base z (Set.Iio δ) = ⊤)
    (S : Set Ordinal.{u}) (hS : S ⊆ Set.Iio δ) (hclosed : DependencyClosed I S) :
    PureUEP (generatedFamily base z S).subtype :=
  subalgebraSubtype_pureUEP_of_top _ _ (generatedFamily_mono base z hS) hgen
    (literal_dependency_closed_pureUEP base z Q active I δ hI hdata hpeak hchrono
      hinactive hne h0 htrace S hS hclosed)

include hI hdata hpeak hchrono hinactive hne h0 htrace in

theorem literal_countable_determination
    (hIc : ∀ k < δ, (I k).Countable) (hbase : TopologicalSpace.IsSeparable base)
    (hgen : generatedFamily base z (Set.Iio δ) = ⊤)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set Ordinal.{u}, S.Countable ∧ S ⊆ Set.Iio δ ∧ DependencyClosed I S ∧
      TopologicalSpace.IsSeparable (generatedFamily base z S : Set A) ∧
      IsSimpleCStar (generatedFamily base z S) ∧
      IsPureState (restrictState (generatedFamily base z S).subtype f) ∧
      StateExtensionUnique (generatedFamily base z S).subtype
        (restrictState (generatedFamily base z S).subtype f) := by
  let e : δ.ToType → Ordinal.{u} := fun k => (k : Ordinal.{u})
  have hei : Function.Injective e := by
    intro a b h
    exact Ordinal.ToType.mk.symm.injective (Subtype.ext h)
  have her : Set.range e = Set.Iio δ := by
    ext k
    constructor
    · rintro ⟨j,rfl⟩
      exact j.toOrd.property
    · intro hk
      exact ⟨Ordinal.ToType.mk ⟨k,hk⟩,by simp [e,Ordinal.ToType.toOrd]⟩
  let J : δ.ToType → Set δ.ToType := fun k => e ⁻¹' I (e k)
  have hJ : ∀ k, (J k).Countable := fun k => (hIc (e k) k.toOrd.property).preimage hei
  have hgen' : generatedFamily base (z ∘ e) Set.univ = ⊤ := by
    rw [generatedFamily_reindex,Set.image_univ,her,hgen]
  obtain ⟨R,hR,hdep,hRp⟩ := generatedFamily_countable_pure_restriction base (z ∘ e)
    hbase hgen' J hJ f hf
  let S := e '' R
  have hS : S ⊆ Set.Iio δ := fun _ hx => her ▸ Set.mem_range.mpr ⟨hx.choose,hx.choose_spec.2⟩
  have hSd : DependencyClosed I S := by
    intro k hk j hj
    obtain ⟨r,hr,rfl⟩ := hk
    have hjδ : j < δ := (hI (e r) r.toOrd.property hj).trans r.toOrd.property
    let q : δ.ToType := Ordinal.ToType.mk ⟨j,hjδ⟩
    have hq : e q = j := by simp [q,e,Ordinal.ToType.toOrd]
    exact ⟨q,hdep r hr (by change e q ∈ I (e r); rwa [hq]),hq⟩
  have hps : IsPureState (restrictState (generatedFamily base z S).subtype f) := by
    exact subalgebra_pureRestriction_congr _ _ (generatedFamily_reindex base z e R) f hRp
  have hsimp := dependency_closed_retained_simple base z Q active S I δ hS hSd
    (fun k hk _ => hI k hk) hdata hpeak hchrono hinactive hne h0
  have hsimp' : IsSimpleCStar (generatedFamily base z S) := by
    apply (subalgebra_simple_congr _ _ ?_).mp hsimp
    change generatedFamily base z (S ∪ Set.Iio 0) = _
    rw [show Set.Iio (0:Ordinal.{u}) = ∅ by ext x; simp, Set.union_empty]

  refine ⟨S,hR.image e,hS,hSd,generatedFamily_separable base z hbase (hR.image e),hsimp',hps,?_⟩
  exact literal_dependency_closed_ambientUEP base z Q active I δ hI hdata hpeak hchrono
    hinactive hne h0 htrace hgen S hS hSd _ hps

end PeakingPairData
end

section

universe u v
open Cardinal Topology TopologicalSpace

theorem countableSubsets_le_continuum (I : Type u) (hI : #I ≤ 𝔠) :
    #({s : Set I // s.Countable}) ≤ 𝔠 := by
  have h := Cardinal.mk_bounded_set_le I ℵ₀
  simp only [Cardinal.le_aleph0_iff_set_countable] at h
  exact h.trans ((Cardinal.power_le_power_right
    (max_le hI Cardinal.aleph0_le_continuum)).trans_eq Cardinal.continuum_power_aleph0)

theorem cardinal_of_countable_determination {A : Type v} (I P : Type u)
    (q : I → ℕ → A) (value : P → A → ℂ) (hI : #I ≤ 𝔠)
    (hdet : ∀ f : P, ∃ i : I, ∀ g : P,
      (∀ n, value f (q i n) = value g (q i n)) → f = g) : #P ≤ 𝔠 := by
  classical
  choose index hindex using hdet
  let code (f : P) : I × (ℕ → ℂ) := (index f,fun n => value f (q (index f) n))
  have hinj : Function.Injective code := by
    intro f g h
    have hi := congrArg Prod.fst h
    have hv := congrArg Prod.snd h
    apply hindex f g
    intro n
    have hh := congrFun hv n
    change value f (q (index f) n) = value g (q (index g) n) at hh
    change index f = index g at hi
    simpa only [← hi] using hh
  apply (Cardinal.mk_le_of_injective hinj).trans
  simp only [Cardinal.mk_prod,Cardinal.mk_arrow,Cardinal.mk_nat,Cardinal.mk_complex,
    Cardinal.lift_continuum,Cardinal.lift_id,
    Cardinal.continuum_power_aleph0]
  have hh : Cardinal.lift.{0,u} #I ≤ 𝔠 := by
    simpa only [Cardinal.lift_continuum] using (Cardinal.lift_le.mpr hI :
      Cardinal.lift.{0,u} #I ≤ Cardinal.lift.{0,u} 𝔠)
  exact (mul_le_mul' hh le_rfl).trans_eq Cardinal.continuum_mul_self

theorem continuous_eq_of_dense_values {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] (q : ℕ → X) (hq : DenseRange q)
    (f g : X → Y) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ n, f (q n) = g (q n)) : f = g :=
  hq.equalizer hf hg (funext h)

theorem continuousMaps_le_continuum (X : Type u) [TopologicalSpace X]
    [SeparableSpace X] [Nonempty X] : #C(X,ℂ) ≤ 𝔠 := by
  classical
  let q := TopologicalSpace.denseSeq X
  let code (f : C(X,ℂ)) : ULift.{u} (ℕ → ℂ) := ⟨fun n => f (q n)⟩
  have hi : Function.Injective code := by
    intro f g h
    apply ContinuousMap.coe_injective
    apply continuous_eq_of_dense_values q (TopologicalSpace.denseRange_denseSeq X)
      f g f.continuous g.continuous
    exact congrFun (congrArg ULift.down h)
  have hh := Cardinal.mk_le_of_injective hi
  simpa only [Cardinal.mk_uLift,Cardinal.mk_arrow,Cardinal.mk_nat,Cardinal.mk_complex,Cardinal.lift_aleph0,
    Cardinal.lift_continuum,Cardinal.continuum_power_aleph0,Cardinal.lift_id] using hh

end

open Cardinal Topology TopologicalSpace
section
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

theorem generatedFamily_pureStates_le_continuum {J : Type}
    (base : Set A) (z : J → A) (hbase : IsSeparable base) (hJ : #J ≤ 𝔠)
    (hdet : ∀ (f : A →L[ℂ] ℂ), IsPureState f →
      ∃ S : Set J, S.Countable ∧
        StateExtensionUnique (generatedFamily base z S).subtype
          (restrictState (generatedFamily base z S).subtype f)) :
    #({f : A →L[ℂ] ℂ // IsPureState f}) ≤ 𝔠 := by
  classical
  let C := {S : Set J // S.Countable}
  let B (S : C) := generatedFamily base z S.val
  let (S : C) : SeparableSpace (B S) :=
    (generatedFamily_separable base z hbase S.property).separableSpace
  let q (S : C) (n : ℕ) : A := (denseSeq (B S) n : A)
  apply cardinal_of_countable_determination C {f : A →L[ℂ] ℂ // IsPureState f}
    q (fun f a => f.val a) (countableSubsets_le_continuum J hJ)
  intro f
  obtain ⟨S,hS,hU⟩ := hdet f.val f.property
  refine ⟨⟨S,hS⟩,fun g hfg => ?_⟩
  have he : restrictState (B ⟨S,hS⟩).subtype f.val =
      restrictState (B ⟨S,hS⟩).subtype g.val := by
    apply DFunLike.ext'
    exact continuous_eq_of_dense_values (denseSeq (B ⟨S,hS⟩))
      (denseRange_denseSeq (B ⟨S,hS⟩))
      (restrictState (B ⟨S,hS⟩).subtype f.val) (restrictState (B ⟨S,hS⟩).subtype g.val)
      (restrictState (B ⟨S,hS⟩).subtype f.val).continuous
      (restrictState (B ⟨S,hS⟩).subtype g.val).continuous hfg
  apply Subtype.ext
  exact hU _ _ f.property.1 g.property.1 rfl he.symm

end

open Cardinal Topology TopologicalSpace
section
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

lemma subalgebra_uniqueRestriction_congr (S T : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)] (hST : S = T)
    (f : A →L[ℂ] ℂ)
    (h : StateExtensionUnique S.subtype (restrictState S.subtype f)) :
    StateExtensionUnique T.subtype (restrictState T.subtype f) := by
  subst T
  exact h

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable [PartialOrder A] [StarOrderedRing A]
variable
    (base : Set A) (z : Ordinal.{0} → A) (Q : Ordinal.{0} → PeakingPairData A)
    (active : Set Ordinal.{0}) (I : Ordinal.{0} → Set Ordinal.{0}) (δ : Ordinal.{0})
    (hI : ∀ k < δ, I k ⊆ Set.Iio k)
    (hdata : ∀ k < δ, k ∈ active → ∀ i n, (Q k).peak i n ∈ generatedFamily base z (I k))
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base z (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base z (Set.Iio k)) (hpeak k hk)
        (z k) (generatedFamily base z (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → z k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base z (Set.Iio k)) (hpeak k hk))
    (h0 : IsSimpleCStar (generatedFamily base z (Set.Iio 0)))
    (htrace : ∀ j < δ, ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a)

include hI hdata hpeak hchrono hinactive hne h0 htrace in

theorem literal_pureStates_le_continuum
    (hIc : ∀ k < δ, (I k).Countable) (hbase : IsSeparable base)
    (hgen : generatedFamily base z (Set.Iio δ) = ⊤) (hδ : δ.card ≤ 𝔠) :
    #({f : A →L[ℂ] ℂ // IsPureState f}) ≤ 𝔠 := by
  let e : δ.ToType → Ordinal.{0} := fun k => (k : Ordinal.{0})
  have hei : Function.Injective e := by
    intro a b h
    exact Ordinal.ToType.mk.symm.injective (Subtype.ext h)
  have her : Set.range e = Set.Iio δ := by
    ext k
    constructor
    · rintro ⟨j,rfl⟩
      exact j.toOrd.property
    · intro hk
      exact ⟨Ordinal.ToType.mk ⟨k,hk⟩,by simp [e,Ordinal.ToType.toOrd]⟩
  apply generatedFamily_pureStates_le_continuum base (z ∘ e) hbase
    (by rwa [Cardinal.mk_toType])
  intro f hf
  obtain ⟨S,hSc,hS,_,_,_,_,hU⟩ := literal_countable_determination
    base z Q active I δ hI hdata hpeak hchrono hinactive hne h0 htrace hIc hbase hgen f hf
  refine ⟨e ⁻¹' S,hSc.preimage hei,?_⟩
  apply subalgebra_uniqueRestriction_congr (generatedFamily base z S) _ ?_ f hU
  rw [generatedFamily_reindex]
  have heS : e '' (e ⁻¹' S) = S := Set.image_preimage_eq_of_subset (her ▸ hS)
  rw [heS]

end PeakingPairData

theorem exists_pureState_list (K : Type) (hK : 𝔠 ≤ #K)
    (hcount : #({f : A →L[ℂ] ℂ // IsPureState f}) ≤ 𝔠)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ l : K → A →L[ℂ] ℂ, (∀ k, IsPureState (l k)) ∧
      ∀ g : A →L[ℂ] ℂ, IsPureState g → ∃ k, l k = g := by
  classical
  let P := {g : A →L[ℂ] ℂ // IsPureState g}
  let : Nonempty P := ⟨⟨f,hf⟩⟩
  obtain ⟨e⟩ := (Cardinal.le_def P K).mp (hcount.trans hK)
  let l : K → P := Function.invFun e
  have hl : Function.Surjective l := Function.invFun_surjective e.injective
  refine ⟨fun k => (l k).val,fun k => (l k).property,fun g hg => ?_⟩
  obtain ⟨k,hk⟩ := hl ⟨g,hg⟩
  exact ⟨k,congrArg Subtype.val hk⟩

end

end NaimarkZFC

end

end OAI
