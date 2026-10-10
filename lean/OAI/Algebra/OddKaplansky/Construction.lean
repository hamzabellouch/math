import OAI.Algebra.OddKaplansky.IndexCut

namespace OAI

universe portUniverse1

section
namespace OddKaplansky.Construction
noncomputable section
local instance constructionDecidableEq (α : Type portUniverse1) : DecidableEq α := Classical.decEq α
open scoped Classical BigOperators Matrix
open SourceGluing SourceGraph
local notation "M" => SourceGluing.modulus
local notation "p" => SourceGluing.p
local notation "HH" => SourceGluing.H
local notation "G₀" => SourceGluing.G₀
lemma prime_large : 1200<p := sourceM_large.trans_lt p_gt
lemma p_ne_two : p≠2 := by have := prime_large; omega
lemma p_odd : Odd p := by rw [SourceGluing.p_def]; exact sourcePrime_odd
lemma minus_square : IsSquare (-1 : ZMod p) := by
  have hd : p∣(Nat.factorial sourceM)^2+1 := by rw [SourceGluing.p_def]; exact sourcePrime_dvd
  exact neg_one_isSquare_of_dvd p (Nat.factorial sourceM) hd
lemma modulus_eq : M+1=p^4 := by
  unfold SourceGluing.modulus
  have hp : 1≤p^4 := Nat.one_le_pow 4 p (by have := prime_large; omega)
  omega
def ell := (p-1)/2
lemma pell : p=2*ell+1 := by
  obtain ⟨k,hk⟩ := p_odd
  unfold ell
  omega
lemma ell_le : ell≤p-ell := by have := pell; omega

variable {K : Type} [Field K] [sectionInstance78 : Fintype K] [sectionInstance79 : CharP K p]
lemma modulus_cast
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p] : (M : K) ≠ 0 := by
  have hc := congrArg (fun n : ℕ => (n : K)) modulus_eq
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,CharP.cast_eq_zero K p,zero_pow (by decide : 4≠0)] at hc
  intro hz
  rw [hz,zero_add] at hc
  exact one_ne_zero hc
lemma cyclic_card : (Fintype.card (Fourier.C M) : K)≠0 := by simpa [Fourier.C] using modulus_cast (K := K)
lemma sector_base_card : (Fintype.card (WreathFourier.Base (H := HH) M) : K)≠0 := by
  simp only [WreathFourier.Base,Fintype.card_fun,Fourier.C,Fintype.card_multiplicative,ZMod.card,Nat.cast_pow]
  exact pow_ne_zero _ (modulus_cast (K := K))
lemma field_units_card
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p] (hK : Fintype.card K=p^4) : Fintype.card Kˣ=M := by
  rw [Fintype.card_units,hK]
  unfold SourceGluing.modulus
  rfl
lemma local_lamp : WreathFourier.base M (WreathFourier.lamp (H := ModularSource.P p) M)=LocalGroup.c p M := by
  ext x
  · by_cases hx : x=1
    · subst x; simp [WreathFourier.base,WreathFourier.lamp,LocalGroup.c]
    · have hx' : x.toAdd ≠ 0 := hx
      simp [WreathFourier.base,WreathFourier.lamp,LocalGroup.c,hx]
  · rfl
lemma local_conjugate
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p] (s : ModularSource.P p) :
    WreathFourier.baseElt (K := K) M (WreathFourier.lamp (H := ModularSource.P p) M)*WreathFourier.topElt M s*WreathFourier.baseElt M (WreathFourier.lamp (H := ModularSource.P p) M)⁻¹=
      MonoidAlgebra.single (LocalGroup.v p M s) 1 := by
  simp only [WreathFourier.baseElt,WreathFourier.topElt,MonoidAlgebra.single_mul_single,one_mul,map_inv,local_lamp]
  rfl

structure LocalDatum where
  e : MonoidAlgebra K HH
  idem : e*e=e
  leftAnn : ∀ s : ModularSource.P p, (MonoidAlgebra.single (LocalGroup.u p M s) 1-1)^ell*e=0
  rightAnn : ∀ s : ModularSource.P p, e*(MonoidAlgebra.single (LocalGroup.v p M s) 1-1)^ell=0
  rank : Fintype.card HH<96*Module.finrank K (LinearMap.range (Algebra.lmul K _ e))
lemma localDatum_exists {ζ : K} (hζ : IsPrimitiveRoot ζ M) (hK : Fintype.card K=p^4) : Nonempty (LocalDatum (K := K)) := by
  obtain ⟨e,he,hann,hrank⟩ := ModularSource.exists_idempotent (K := K) p M ell hζ
    (by have := prime_large; omega) pell modulus_eq (field_units_card hK)
  refine ⟨⟨e,he,?_,?_,?_⟩⟩
  · intro s
    exact (hann s).1
  · intro s
    simpa only [local_conjugate] using (hann s).2
  · convert hrank using 1

def prescribedLocalDatum {ζ : K} (hζ : IsPrimitiveRoot ζ M) (hK : Fintype.card K=p^4) : LocalDatum (K := K) where
  e := ModularSource.explicitElement p M ell hζ
  idem := (ModularSource.explicit_properties p M ell hζ (by have := prime_large; omega) pell modulus_eq (field_units_card hK)).1
  leftAnn s := (ModularSource.explicit_properties p M ell hζ (by have := prime_large; omega) pell modulus_eq (field_units_card hK)).2.1 s |>.1
  rightAnn s := by
    simpa only [local_conjugate] using (ModularSource.explicit_properties p M ell hζ (by have := prime_large; omega) pell modulus_eq (field_units_card hK)).2.1 s |>.2
  rank := by
    exact (ModularSource.explicit_properties p M ell hζ (by have := prime_large; omega) pell modulus_eq (field_units_card hK)).2.2

def push (v : Vertex) : MonoidAlgebra K HH →ₐ[K] MonoidAlgebra K G₀ := MonoidAlgebra.mapDomainAlgHom K K (SourceGluing.vertex v)
lemma ordered_zero
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p] (d : LocalDatum (K := K)) (v w : Vertex) (hvw : v<w) (hvwadj : graph.Adj v w) : push v d.e*push w d.e=0 := by
  let edge : SourceGraph.Edge := ⟨(v,w),hvw,hvwadj⟩
  have hleft : SourceGluing.edgeHom v edge=LocalGroup.edgeHom p M true (index w) := by
    simp [SourceGluing.edgeHom,SourceGraph.neighbor,GraphEdges.neighbor,edge]
  have hright : SourceGluing.edgeHom w edge=LocalGroup.edgeHom p M false (index v) := by
    have hne : w≠v := ne_of_gt hvw
    simp [SourceGluing.edgeHom,SourceGraph.neighbor,GraphEdges.neighbor,edge,hne]
  apply OrderedZero.product_zero p ell ell_le
    (SourceGluing.edgeHom v edge) (by rw [hleft]; exact LocalGroup.edgeHom_injective p M true _) (SourceGluing.edgeHom w edge)
    (SourceGluing.vertex v) (SourceGluing.vertex w)
  · exact Gluing.edge_eq SourceGraph.Inc SourceGluing.edgeHom edge v w (CyclicAlgebra.gen p) (Or.inl rfl) (Or.inr rfl)
  · rw [hleft]
    exact d.rightAnn ((LocalGroup.line p (index w)).toMultiplicative (CyclicAlgebra.gen p))
  · rw [hright]
    exact d.leftAnn ((LocalGroup.line p (index v)).toMultiplicative (CyclicAlgebra.gen p))
end
end OddKaplansky.Construction

end

end OAI
