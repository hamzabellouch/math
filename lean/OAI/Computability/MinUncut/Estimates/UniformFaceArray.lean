import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformEquation
import OAI.Computability.MinUncut.Machines.UniformAlphabet

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Alphabet
open MinUncut.Inner MinUncut.FiniteProof MinUncut.Outer
open UEncoding
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((MinUncutGames.Foundations.Hastad.SourceOccurrences.Encoding.fin (t p)).function
  MinUncutGames.Foundations.Hastad.SourceOccurrences.Encoding.bool).code (h p)).val))
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
def arrays : UEncoding P (fun p=>FaceArray (LocalTemplate.Alphabet (h p)) (m p) (n p)) :=
  (Face.rows m n hm hn hnpos).function (forms t ht h hc)
lemma map_labelCode : ((arrays t ht h hc m n hm hn hnpos).prod (labels t ht h hc)).Map
    (Face.codes m n hm hn hnpos) (fun _ x=>labelCode x.1 x.2) := by
  let r:=Face.rows m n hm hn hnpos
  let a:=arrays t ht h hc m n hm hn hnpos
  let l:=labels t ht h hc
  let c:=a.prod l
  have hb : (c.prod r).Map a (fun _ x=>x.1.1) := (map_fst _ _).first
  have hx : (c.prod r).Map l (fun _ x=>x.1.2) := (map_snd _ _).first
  have he : c.Map (r.function (field P)) (fun _ x r=>(x.1 r) x.2) :=
    map_lambda (map_comp (map_pair (map_apply hb (map_snd _ _)) hx) (map_forms_apply t ht h hc))
  exact Face.map_codeMk m n hm hn hnpos
    (map_comp he (Face.map_faceSum m n hm hn hnpos)) (by intro p x; exact ⟨_,rfl⟩)
end MinUncut.Preprocess.Alphabet

end
end

end OAI
