import OAI.Algebra.OddKaplansky.Construction

namespace OAI

universe portUniverse1

section
namespace OddKaplansky.Construction
noncomputable section
local instance sectorConstructionDecidableEq (α : Type portUniverse1) : DecidableEq α := Classical.decEq α
open scoped Classical BigOperators Matrix
open SourceGluing SourceGraph
local notation "M" => SourceGluing.modulus
local notation "p" => SourceGluing.p
local notation "HH" => SourceGluing.H
abbrev G₁ := SectorGroup.G₁ M SourceGluing.vertex
instance : Group.FG G₁ := inferInstance
variable {K : Type} [Field K] [sectionInstance80 : Fintype K] [sectionInstance81 : CharP K p]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
abbrev R := MonoidAlgebra K G₁
def f : R (K := K) := SectorGroup.f M SourceGluing.vertex hζ
lemma f_idem : f hζ*f hζ=f hζ := SectorGroup.f_idempotent M SourceGluing.vertex hζ cyclic_card
lemma f_nonzero : f hζ≠0 := SectorGroup.f_ne_zero M SourceGluing.vertex hζ SourceGluing.vertex_injective cyclic_card
lemma f_commute
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{0} K (@CommRing.toCommMonoid.{0} K (@Field.toCommRing.{0} K contextInstance1)) ζ
  OddKaplansky.SourceGluing.modulus) (a : R (K := K)) : Commute (f hζ) a := SectorGroup.f_central M SourceGluing.vertex hζ a
def original : MonoidAlgebra K SourceGluing.G₀ →ₐ[K] R (K := K) := MonoidAlgebra.mapDomainAlgHom K K (SectorGroup.original M SourceGluing.vertex)
def attached (v : Vertex) : MonoidAlgebra K (WreathFourier.Wreath (H := HH) M) →ₐ[K] R (K := K) :=
  MonoidAlgebra.mapDomainAlgHom K K (SectorGroup.factor M SourceGluing.vertex v)
def P (d : LocalDatum (K := K)) (v : Vertex) : R (K := K) := f hζ*original (push v d.e)
lemma f_mul_product (x y : R (K := K)) : (f hζ*x)*(f hζ*y)=f hζ*(x*y) := by
  calc
    _ = f hζ*(x*f hζ)*y := by simp only [mul_assoc]
    _ = f hζ*(f hζ*x)*y := by rw [← (f_commute hζ x).eq]
    _ = (f hζ*f hζ)*(x*y) := by simp only [mul_assoc]
    _ = _ := by rw [f_idem]
lemma P_idem (d : LocalDatum (K := K)) (v : Vertex) : P hζ d v*P hζ d v=P hζ d v := by
  rw [P,f_mul_product,← map_mul,← map_mul,d.idem]
lemma P_sector (d : LocalDatum (K := K)) (v : Vertex) : f hζ*P hζ d v=P hζ d v := by rw [P,← mul_assoc,f_idem]
lemma P_ordered (d : LocalDatum (K := K)) (v w : Vertex) (hvw : v<w) (hadj : graph.Adj v w) : P hζ d v*P hζ d w=0 := by
  rw [P,P,f_mul_product,← map_mul,ordered_zero d v w hvw hadj,map_zero,mul_zero]
lemma fit_upper (d : LocalDatum (K := K)) (v w : Vertex) (hvw : v<w) :
    (∑ T : SourceFit.Slot, SourceFit.alpha (K := K) v T*SourceFit.beta w T) • (P hζ d v*P hζ d w)=0 := by
  by_cases ha : graph.Adj v w
  · rw [P_ordered hζ d v w hvw ha,smul_zero]
  · change SourceFit.fitting v w • _=0
    rw [SourceFit.fitting_nonedge v w (ne_of_lt hvw) ha,zero_smul]

abbrev W := Fin (Fintype.card HH)
abbrev N (d : LocalDatum (K := K)) := Fin (Module.finrank K (LinearMap.range (Algebra.lmul K _ d.e)))
structure Rectangular (d : LocalDatum (K := K)) where
  J : Vertex → Matrix W (N d) (R (K := K))
  Y : Vertex → Matrix (N d) W (R (K := K))
  YJ : ∀ v, Y v*J v=Matrix.diagonal (fun _ => f hζ)
  JY : ∀ v, J v*Y v=Matrix.diagonal (fun _ => P hζ d v)
  sectorJ : ∀ v w n, f hζ*J v w n=J v w n
  sectorY : ∀ v n w, f hζ*Y v n w=Y v n w
lemma rectangular_exists (d : LocalDatum (K := K)) : Nonempty (Rectangular hζ d) := by
  obtain ⟨J,Y,hYJ,hJY,hJ,hY⟩ := SourceSector.rectangular M p hζ sector_base_card cyclic_card d.e d.idem
    (W := W) (N := N d) (Fintype.card_fin _) (Fintype.card_fin _)
  let Js (v : Vertex) := J.map (attached (K := K) v)
  let Ys (v : Vertex) := Y.map (attached (K := K) v)
  have hff (v : Vertex) : attached (K := K) v (SectorFourier.f M hζ)=f hζ := SectorGroup.factor_f M SourceGluing.vertex hζ v
  have hee (v : Vertex) : attached (K := K) v (MonoidAlgebra.mapDomainAlgHom K K (WreathFourier.top M) d.e)=original (push v d.e) :=
    SectorGroup.factor_original M SourceGluing.vertex v d.e
  refine ⟨⟨Js,Ys,?_,?_,?_,?_⟩⟩
  · intro v
    dsimp [Js,Ys]
    rw [← Matrix.map_mul,hYJ]
    funext i j
    by_cases he : i=j <;> simp [Matrix.map_apply,he,hff]
  · intro v
    dsimp [Js,Ys]
    rw [← Matrix.map_mul,hJY]
    funext i j
    by_cases he : i=j
    · subst j
      simp only [Matrix.map_apply,Matrix.diagonal_apply_eq,map_mul,hff,hee,P]
    · simp [Matrix.map_apply,he]
  · intro v w n
    change f hζ*attached v (J w n)=attached v (J w n)
    rw [← hff,← map_mul,hJ]
  · intro v n w
    change f hζ*attached v (Y n w)=attached v (Y n w)
    rw [← hff,← map_mul,hY]

def prescribedRectangles (d : LocalDatum (K := K)) : Rectangular hζ d := by
  let J := OrderedSourceSector.explicitJ M p hζ d.e d.idem (W := W) (N := N d) (Fintype.card_fin _) (Fintype.card_fin _)
  let Y := OrderedSourceSector.explicitY M p hζ d.e d.idem (W := W) (N := N d) (Fintype.card_fin _) (Fintype.card_fin _)
  have hs := OrderedSourceSector.explicit_properties M p hζ d.e d.idem (W := W) (N := N d) (Fintype.card_fin _) (Fintype.card_fin _) sector_base_card cyclic_card
  obtain ⟨hYJ,hJY,hJ,hY⟩ := hs
  let Js (v : Vertex) := J.map (attached (K := K) v)
  let Ys (v : Vertex) := Y.map (attached (K := K) v)
  have hff (v : Vertex) : attached (K := K) v (SectorFourier.f M hζ)=f hζ := SectorGroup.factor_f M SourceGluing.vertex hζ v
  have hee (v : Vertex) : attached (K := K) v (MonoidAlgebra.mapDomainAlgHom K K (WreathFourier.top M) d.e)=original (push v d.e) :=
    SectorGroup.factor_original M SourceGluing.vertex v d.e
  refine ⟨Js,Ys,?_,?_,?_,?_⟩
  · intro v
    dsimp [Js,Ys]
    rw [← Matrix.map_mul,hYJ]
    funext i j
    by_cases he : i=j <;> simp [Matrix.map_apply,he,hff]
  · intro v
    dsimp [Js,Ys]
    rw [← Matrix.map_mul,hJY]
    funext i j
    by_cases he : i=j
    · subst j
      simp only [Matrix.map_apply,Matrix.diagonal_apply_eq,map_mul,hff,hee,P]
    · simp [Matrix.map_apply,he]
  · intro v w n
    change f hζ*attached v (J w n)=attached v (J w n)
    rw [← hff,← map_mul,hJ]
  · intro v n w
    change f hζ*attached v (Y n w)=attached v (Y n w)
    rw [← hff,← map_mul,hY]

def ix : Vertex ≃o Fin (Fintype.card Vertex) := (Fintype.orderIsoFinOfCardEq Vertex rfl).symm
abbrev Small := W×SourceFit.Slot
abbrev Large (d : LocalDatum (K := K)) := Vertex×N d
def C (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix Small (Large d) (R (K := K)) :=
  Compression.Csharp (K := K) (P hζ d) SourceFit.beta rect.J
def D (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix (Large d) Small (R (K := K)) :=
  Compression.Dsharp (K := K) (P hζ d) SourceFit.alpha SourceFit.beta rect.Y
lemma DC (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : D hζ d rect*C hζ d rect=Matrix.diagonal (fun _ => f hζ) := by
  have hdiag (v : Vertex) : ∑ t, SourceFit.alpha (K := K) v t*SourceFit.beta v t=1 := SourceFit.fitting_diagonal p prime_large v
  have hu (v w : Vertex) (hvw : (ix v).val < (ix w).val) :
      (∑ t, SourceFit.alpha (K := K) v t*SourceFit.beta w t) • (P hζ d v*P hζ d w)=0 :=
    fit_upper hζ d v w (ix.lt_iff_lt.mp hvw)
  have hyj : ∀ v, rect.Y v*rect.J v= @Matrix.diagonal (N d) (R (K := K)) (Classical.decEq _) _ (fun _ => f hζ) := by
    intro v
    convert rect.YJ v using 1 ; congr ; exact Subsingleton.elim _ _
  have hjy : ∀ v, rect.J v*rect.Y v= @Matrix.diagonal W (R (K := K)) (Classical.decEq _) _ (fun _ => P hζ d v) := by
    intro v
    convert rect.JY v using 1 ; congr ; exact Subsingleton.elim _ _
  convert Compression.compressed (K := K) (f hζ) (f_idem hζ) (P hζ d) (P_idem hζ d)
    SourceFit.alpha SourceFit.beta ix ix.injective hdiag hu rect.J rect.Y hyj hjy using 1 <;> congr ; exact Subsingleton.elim _ _
lemma DC_classical (d : LocalDatum (K := K)) (rect : Rectangular hζ d) :
    D hζ d rect*C hζ d rect= @Matrix.diagonal (Large d) (R (K := K)) (Classical.decEq _) _ (fun _ => f hζ) := by
  convert DC hζ d rect using 1 ; congr ; exact Subsingleton.elim _ _
lemma C_sector (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : ∀ a b, f hζ*C hζ d rect a b=C hζ d rect a b :=
  Compression.Csharp_sector (K := K) (f hζ) (P hζ d) (P_sector hζ d) SourceFit.beta rect.J
lemma D_sector
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p]
    {ζ : K}
    (hζ : @IsPrimitiveRoot.{0} K (@CommRing.toCommMonoid.{0} K (@Field.toCommRing.{0} K contextInstance1)) ζ
  OddKaplansky.SourceGluing.modulus) (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : ∀ a b, f hζ*D hζ d rect a b=D hζ d rect a b :=
  Compression.Dsharp_sector (K := K) (f hζ) (P hζ d) SourceFit.alpha SourceFit.beta rect.Y rect.sectorY
lemma d_positive
    {K : Type}
    [contextInstance1 : Field.{0} K]
    [Fintype.{0} K]
    [@CharP.{0} K
  (@AddGroupWithOne.toAddMonoidWithOne.{0} K
    (@Ring.toAddGroupWithOne.{0} K (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K contextInstance1))))
  OddKaplansky.SourceGluing.p] (d : LocalDatum (K := K)) : 0<Fintype.card (N d) := by
  rw [Fintype.card_fin]
  have := d.rank
  omega
lemma sizes (d : LocalDatum (K := K)) : Fintype.card Small<Fintype.card (Large d) := by
  have ht := SourceFit.ratio_bound
  have hd := d.rank
  have hdpos := d_positive d
  simp only [N,Fintype.card_fin] at hdpos
  have hh := Nat.mul_le_mul_right (Fintype.card SourceFit.Slot) hd.le
  have hhh := Nat.mul_lt_mul_of_pos_right ht hdpos
  simp only [Small,Large,W,N,Fintype.card_prod,Fintype.card_fin,SourceGraph.card_vertices]
  nlinarith
lemma small_positive : 0<Fintype.card Small := by
  have ht : Nonempty SourceFit.Slot := ⟨⟨∅,by simp⟩⟩
  have hw : 0<Fintype.card HH := Fintype.card_pos
  simp only [Small,W,Fintype.card_prod,Fintype.card_fin]
  exact Nat.mul_pos hw (Fintype.card_pos_iff.mpr ht)
end
end OddKaplansky.Construction

end

end OAI
