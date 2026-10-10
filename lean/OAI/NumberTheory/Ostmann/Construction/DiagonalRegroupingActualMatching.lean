import OAI.NumberTheory.Ostmann.Construction.DiagonalRegroupingRootCorrection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

theorem remainingIntegrand_diagonal_matching (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v w : AllowedFrequency V l)
    (hx : remainingIntegrand d P sources seed V giant X G bins outside l p u x v≠0)
    (hy : remainingIntegrand d P sources seed V giant X G bins outside l p u y w≠0)
    (hlargeX : ∀q∈remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant x,V l<q)
    (hlargeY : ∀q∈remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant y,V l<q)
    (htag : remainingExactTag sources (Template.remainder (l+1) (Template.current seed l)) giant x v.val=
      remainingExactTag sources (Template.remainder (l+1) (Template.current seed l)) giant y w.val) :
    v=w ∧ remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant x=
      remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant y ∧
    ∃! e : Fin (remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant x).length ≃
        Fin (remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant y).length,
      ∀i,(remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant y).get (e i)=
        (remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant x).get i := by
  have hfx := (remainingIntegrand_root_support d P sources seed V giant X G bins outside l p u x v hx).2.2.2.2
  have hfy := (remainingIntegrand_root_support d P sources seed V giant X G bins outside l p u y w hy).2.2.2.2
  have he := (remainingExactTag_eq_iff sources _ giant x y hfx.1 hfy.1
    (fun q hq => hfx.2.trans_lt (hlargeX q hq))
    (fun q hq => hfy.2.trans_lt (hlargeY q hq))).mp htag
  refine ⟨Subtype.ext he.1,he.2,?_⟩
  exact existsUnique_value_matching
    (remainingValues_nodup_of_integrand_ne_zero d P sources seed V giant X G bins outside l p u x v hx)
    (remainingValues_nodup_of_integrand_ne_zero d P sources seed V giant X G bins outside l p u y w hy)
    (remainingValues_perm_of_product_eq sources _ giant x y he.2)

theorem remaining_giant_eq_of_product_eq (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x y : RemainingSample sources T giant)
    (hsep : ∀i : Fin T.length,Disjoint giant.candidates (sources T[i].origin).candidates)
    (he : remainingProduct sources T giant x=remainingProduct sources T giant y) : x.1.val=y.1.val := by
  have hp := remainingValues_perm_of_product_eq sources T giant x y he
  have hx : x.1.val∈remainingValues sources T giant y := hp.mem_iff.mp List.mem_cons_self
  rcases List.mem_cons.mp hx with he | hx
  · exact he
  · obtain ⟨a,ha,hea⟩ := List.mem_map.mp hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    have hy : x.1.val∈(sources T[i].origin).candidates := by
      simpa only [←hea] using (y.2 i).property
    exact (Finset.disjoint_left.mp (hsep i) x.1.property hy).elim

theorem value_matching_preserves_band {xs ys : List ℕ} {β : Type*}
    (e : Fin xs.length ≃ Fin ys.length) (he : ∀i,ys.get (e i)=xs.get i) (band : ℕ→β) :
    ∀i,band (ys.get (e i))=band (xs.get i) := fun i => congrArg band (he i)

end Ostmann.Construction

end

end OAI
